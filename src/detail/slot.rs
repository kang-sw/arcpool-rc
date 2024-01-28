use std::{
    ptr::{null_mut, NonNull},
    sync::atomic::{
        AtomicPtr, AtomicUsize,
        Ordering::{Acquire, Relaxed, Release},
    },
};

use super::Slot;

pub(super) const HEAD_SOCKET_COUNT: usize = 6;
const ROTATE_AMOUNT: usize = 5;

#[repr(C)]
pub(super) struct Table<T> {
    pop_index: AtomicUsize,
    push_index: AtomicUsize,
    padding: [usize; 14 - HEAD_SOCKET_COUNT],
    elems: [AtomicPtr<Slot<T>>; HEAD_SOCKET_COUNT],
}

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self {
            pop_index: Default::default(),
            push_index: Default::default(),
            padding: Default::default(),
            elems: Default::default(),
        }
    }
}

impl<T> Table<T> {
    pub fn for_each_head(&mut self, mut f: impl FnMut(NonNull<Slot<T>>)) {
        for socket in &self.elems {
            if let Some(ptr) = NonNull::new(socket.load(Relaxed)) {
                f(ptr);
            }
        }
    }

    /// # Safety
    ///
    /// Given element must be exclusively accessible,
    pub unsafe fn push(&self, elem: *mut Slot<T>, tail: Option<&mut Slot<T>>) {
        debug_assert!(!elem.is_null());

        let tail = tail.unwrap_or(&mut *elem) as *mut Slot<T>;
        debug_assert!((*tail).next_free.is_null());

        let mut push_index = self.push_index.fetch_sub(1, Relaxed);

        // - Set order should be Release, to make `next_free` visible to other thread.
        // - We won't care the fetch order

        let update_func = |prev: *mut Slot<T>| {
            if prev as usize == usize::MAX {
                // It is being held by consumer. We should retry pushing later.
                return None;
            }

            (*tail).next_free = prev;
            Some(elem)
        };

        loop {
            let index = push_index % self.elems.len();
            let socket = &self.elems[index];

            if socket.fetch_update(Release, Relaxed, update_func).is_ok() {
                return;
            }

            // If we fail to push element, rotate slot to push by 1.
            push_index = push_index.wrapping_add(1);

            // We're spinning now!
            std::hint::spin_loop();
        }
    }

    pub unsafe fn pop(&self) -> Option<NonNull<Slot<T>>> {
        let mut pop_index = self.pop_index.fetch_sub(1, Relaxed);
        // ^^^ We're using `fetch_sub` to calculating rotate start index. Since every task
        // rotates forward to find available elements, if we increment `self.pop_index` then
        // it'll more likely collide with other thread's ongoing fetch request.

        let mut tried_bits = (1 << self.elems.len()) - 1;

        while tried_bits != 0 {
            let index = pop_index % self.elems.len();
            pop_index = pop_index.wrapping_add(ROTATE_AMOUNT);
            //                                ^^^ This will reduce consumer collision.

            let socket = &self.elems[index];

            // What we're doing here:
            // 1. Get current slot [A] of the socket, and get its next slot [B].
            // 2. Replace socket with its next slot [B].
            //
            // If we do cmpxchg (2) by (1), it's behavior have possible unsoundness when:
            //
            //      a. After 1, another thread successfully popped [A->B], now socket points [B]
            //      b. Then from same socket, another thread pops [B->C], socket is [C]
            //      c. Another thread returns [A] back to same socket. the socket is [A->C]
            //      d. !!! This thread cmpxchg for [A] with [B] which is being USED!
            //
            // Therefore, we need more strong mechanism to notify that we're dealing with this
            // socket. Following is current option:
            //
            //      a. Just withdraw the socket preemptively, making it null.
            //      b. And put the next element back to socket.
            //
            // However, if we just put null pointer on exchange, it's seen as empty free slots for
            // other consumers; which trigger additional unncecessary allocation repeatedly.
            // Therefore, here we're going to mark the slot as 'busy', by setting the pointer value
            // as `usize::MAX`, then do our job, put it back.
            //
            // - If producer see the `busy` slot, it'll be locked and await until it's released.
            // - If consumer see the 'busy' slot, it'll jump to next allocation, not consuming
            //   `max_retry` count.

            // Preemptively occupy the socket.
            let slot = socket.swap(usize::MAX as _, Acquire);

            if slot.is_null() {
                // It's empty slot. Consume one retry and jump to next.
                socket.swap(null_mut(), Release);

                tried_bits &= !(1 << index);
                continue;
            }

            if slot as usize == usize::MAX {
                // It's being held by producer. We should retry popping later, but not consuming the
                // retry bit.
                continue;
            }

            // Now we're sure that the slot is not null, and not being held by any other consumer.
            // Roll back the socket state as soon as possible, and now we can safely deal with
            // popped slot now.
            socket.swap((*slot).next_free, Release);

            // Clear next node.
            (*slot).next_free = null_mut();

            return Some(NonNull::new_unchecked(slot));
        }

        None
    }
}
