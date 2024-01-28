use std::{
    mem::{replace, size_of, transmute, MaybeUninit},
    num::NonZeroUsize,
    ptr::{null_mut, NonNull},
    sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    },
};

use crossbeam_utils::CachePadded;
use parking_lot::Mutex;

pub(crate) mod pool {
    use std::{
        ptr::null_mut,
        sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        },
    };

    use parking_lot::Mutex;

    use super::{Counter, FnApply, FnCreate, PageLock, PoolInnerImpl};

    #[derive(Default)]
    pub struct Builder<T, CreateFn, PrepareFn, CleanFn> {
        _marker_ty: std::marker::PhantomData<T>,
        page_size: usize,
        init_func: CreateFn,
        prepare_func: PrepareFn,
        clean_func: CleanFn,
        use_page_alloc_lock: bool,
        use_item_counter: bool,
    }

    // ==== Builder implementation ====

    impl<T> crate::Pool<T> {
        pub fn builder() -> Builder<T, (), (), ()> {
            Builder {
                _marker_ty: Default::default(),
                page_size: 32, // Default page size
                init_func: (),
                prepare_func: (),
                clean_func: (),
                use_page_alloc_lock: false,
                use_item_counter: false,
            }
        }
    }

    impl<T, CreateFn, PrepareFn, CleanFn> Builder<T, CreateFn, PrepareFn, CleanFn>
    where
        T: 'static + Send,
        CreateFn: FnCreate<T>,
        PrepareFn: FnApply<T>,
        CleanFn: FnApply<T>,
    {
        pub fn finish(self) -> crate::Pool<T> {
            match (self.use_item_counter, self.use_page_alloc_lock) {
                (true, true) => self.finish_with(AtomicCounter::default(), Mutex::new(())),
                (true, false) => self.finish_with(AtomicCounter::default(), ()),
                (false, true) => self.finish_with((), Mutex::new(())),
                (false, false) => self.finish_with((), ()),
            }
        }

        fn finish_with<C: Counter, L: PageLock>(self, counter: C, lock: L) -> crate::Pool<T> {
            let inner = Arc::new(PoolInnerImpl {
                free_head: Mutex::new(null_mut()).into(),
                free_head_may_weak: Mutex::new(null_mut()).into(),
                fallback_page_size: self.page_size.try_into().unwrap(),
                init_func: self.init_func,
                prepare_func: self.prepare_func,
                clean_func: self.clean_func,
                alloc_lock: lock,
                item_counter: counter,
            });

            crate::Pool { inner }
        }
    }

    impl<T, CreateFn, PrepareFn, CleanFn> Builder<T, CreateFn, PrepareFn, CleanFn> {
        /// Specify default page allocation size when [`crate::Pool::checkout`] or
        /// [`crate::Pool::checkout_local`] fails due to lack of available element.
        pub fn with_default_page_size(mut self, page_size: usize) -> Self {
            assert!(page_size > 0, "page size must be greater than zero");

            self.page_size = page_size;
            self
        }

        /// Specify if the page allocation lock is acquired before performing default page
        /// allocation.
        ///
        /// Acquiring the lock isn't mandatory for page allocation, but it's recommended when
        /// default page size is set as large value.
        ///
        /// The allocation process involves executing user-provided initialization logic, which can
        /// have unpredictable execution time. Without the lock, multiple threads might concurrently
        /// see empty free element stacks and allocate pages for each.
        ///
        /// Although this results in excessive memory allocation, all 'extra' allocations will be
        /// added to the free list effectively. Moreover, the user-provided initialization logic
        /// will run concurrently in this scenario. Thus, disabling the allocation lock can be a
        /// valid policy if extensive capacity expansion is preferred.
        pub fn with_page_allocation_lock(mut self, enabled: bool) -> Self {
            self.use_page_alloc_lock = enabled;
            self
        }

        /// Specify whether to use item counter internally. This exposes
        pub fn with_item_counter(mut self, enabled: bool) -> Self {
            self.use_item_counter = enabled;
            self
        }

        /// Specify function which is used when creating new page element from base. It is called
        /// only for once every element slot allocation.
        pub fn with_initializer<F>(self, func: F) -> Builder<T, F, PrepareFn, CleanFn>
        where
            F: Fn() -> T + Send + Sync + 'static,
        {
            Builder {
                _marker_ty: self._marker_ty,
                page_size: self.page_size,
                init_func: func,
                prepare_func: self.prepare_func,
                clean_func: self.clean_func,
                use_page_alloc_lock: self.use_page_alloc_lock,
                use_item_counter: self.use_item_counter,
            }
        }

        /// Specify function which will be invoked every time that the reference is deallocated.
        ///
        /// e.g. cleaning vectors, etc ...
        pub fn with_cleanup<F>(self, func: F) -> Builder<T, CreateFn, PrepareFn, F>
        where
            F: Fn(&mut T) + Send + Sync + 'static,
        {
            Builder {
                _marker_ty: self._marker_ty,
                page_size: self.page_size,
                init_func: self.init_func,
                prepare_func: self.prepare_func,
                clean_func: func,
                use_page_alloc_lock: self.use_page_alloc_lock,
                use_item_counter: self.use_item_counter,
            }
        }

        /// Specify function which is invoked every time you checkout any element from this pool.
        ///
        /// [`Builder::with_cleanup`] and [`Builder::with_prepare`] can be specified both, the
        /// former is releasing resource, and the latter can be used kind of expensive resource
        /// acquiring, etc ..
        pub fn with_prepare<F>(self, func: F) -> Builder<T, CreateFn, F, CleanFn>
        where
            F: Fn(&mut T) + Send + Sync + 'static,
        {
            Builder {
                _marker_ty: self._marker_ty,
                page_size: self.page_size,
                init_func: self.init_func,
                prepare_func: func,
                clean_func: self.clean_func,
                use_page_alloc_lock: self.use_page_alloc_lock,
                use_item_counter: self.use_item_counter,
            }
        }
    }

    // ==== Builder Component: Cleaner Function ====

    impl<T> FnApply<T> for () {
        fn call(&self, _: &mut T) {}
    }

    impl<T, F: Fn(&mut T) + Send + Sync + 'static> FnApply<T> for F {
        fn call(&self, value: &mut T) {
            self(value)
        }
    }

    impl<T: Default> FnCreate<T> for () {
        fn call(&self) -> T {
            T::default()
        }
    }

    impl<T, F: Fn() -> T + Send + Sync + 'static> FnCreate<T> for F {
        fn call(&self) -> T {
            self()
        }
    }

    // ==== Builder Component: Page Lock ====
    impl super::PageLock for () {
        type LockGuard<'a> = ();
        fn acquire_job(&self) -> Self::LockGuard<'_> {}
        fn try_acquire_job(&self) -> Option<Self::LockGuard<'_>> {
            Some(())
        }
    }

    impl super::PageLock for parking_lot::Mutex<()> {
        type LockGuard<'a> = parking_lot::MutexGuard<'a, ()>;

        fn acquire_job(&self) -> Self::LockGuard<'_> {
            self.lock()
        }
        fn try_acquire_job(&self) -> Option<Self::LockGuard<'_>> {
            self.try_lock()
        }
    }

    // ==== Builder Component: Value Counter ====
    #[derive(Default)]
    struct AtomicCounter {
        total: AtomicUsize,
        free: AtomicUsize,
    }

    impl Counter for AtomicCounter {
        fn inc_total_by(&self, total: usize) {
            self.total.fetch_add(total, Ordering::Relaxed);
        }

        fn inc_free_item_by(&self, free: usize) {
            self.free.fetch_add(free, Ordering::Relaxed);
        }

        fn dec_free_item(&self) {
            self.free.fetch_sub(1, Ordering::Relaxed);
        }

        fn total_item(&self) -> Option<usize> {
            Some(self.total.load(Ordering::Relaxed))
        }

        fn free_item(&self) -> Option<usize> {
            Some(self.free.load(Ordering::Relaxed))
        }
    }

    impl Counter for () {
        fn inc_total_by(&self, _: usize) {}
        fn inc_free_item_by(&self, _: usize) {}
        fn dec_free_item(&self) {}

        fn total_item(&self) -> Option<usize> {
            None
        }

        fn free_item(&self) -> Option<usize> {
            None
        }
    }
}

pub(crate) trait PoolInner<T>: Send + Sync + 'static {
    fn checkout_sync(&self) -> NonNull<Slot<T>>;
    fn checkout_local(&self) -> NonNull<Slot<T>>;

    fn allocate_page(&self, page_size: Option<NonZeroUsize>);

    fn num_total_items(&self) -> Option<usize>;
    fn num_free_items(&self) -> Option<usize>;

    fn sync_slot_cleanup_then_checkin(&self, slot_ref: &mut Slot<T>);
    fn sync_slot_dispose(&self, slot_ref: &mut Slot<T>);
    fn local_slot_cleanup(&self, slot_ref: &mut Slot<T>);
    fn local_slot_checkin_then_dispose(&self, slot_ref: &mut Slot<T>);
}

// ========================================================== Pool Inner Impl ===|

struct PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Counter, AllocLock> {
    /// # XXX
    ///
    /// Since the lock-free implementation of this logic is overly complicated and hard to
    /// verify whether it's correctly written or not, just use mutex here. In future, if I
    /// become more advanced to concurrency, then reconsider lock-free implementation again ...
    ///
    // The lock-free implementation should deal with the edge case. Maybe we can adopt slot-wise
    // locks, however, how it differs from this *verified* mutex if it needed to be checked
    // everytime?
    //
    // - (1) -> (2) -> (3) -> (4)
    //   - then [A] cache (2)
    //   - then [B] cache (2), cmpxcg (1)
    // - (2) -> (3) -> (4)
    //   - then [C] cache (3), cmpxcg (2)
    // - (3) -> (4)
    //   - then [B] return (1), cmpxcg (3)
    // - (1) -> (3) -> (4)
    //   - FOR [A], (1) is identical ... but cached (2)
    // - Now head is = (2:INVALID)
    //   - A can detect this; (cache invalidated!)
    //   - But, other thread still tries to access already allocated node 2.
    //   - Need to avoid this situation ... but, how?
    free_head: CachePadded<Mutex<*mut Slot<T>>>,

    /// If only the strong reference was released (in sync) (i.e. any weak reference presents),
    /// the node will be stored here. Only `sync` checkouts are allowed to access this storage,
    /// as the generation based hot reuse is exclusively permitted for atomic versions.
    free_head_may_weak: CachePadded<Mutex<*mut Slot<T>>>,

    fallback_page_size: NonZeroUsize,

    init_func: CreateFn,
    prepare_func: PrepareFn,
    clean_func: CleanFn,

    alloc_lock: AllocLock,

    item_counter: Counter,
}

unsafe impl<T1, T2, T3, T4, T5, T6> Send for PoolInnerImpl<T1, T2, T3, T4, T5, T6> {}
unsafe impl<T1, T2, T3, T4, T5, T6> Sync for PoolInnerImpl<T1, T2, T3, T4, T5, T6> {}

#[doc(hidden)]
pub trait FnApply<T>: 'static + Send + Sync {
    fn call(&self, _: &mut T);
}

pub trait FnCreate<T>: 'static + Send + Sync {
    fn call(&self) -> T;
}

trait PageLock: 'static + Send + Sync {
    type LockGuard<'a>
    where
        Self: 'a;

    fn acquire_job(&self) -> Self::LockGuard<'_>;
    fn try_acquire_job(&self) -> Option<Self::LockGuard<'_>>;
}

trait Counter: 'static + Send + Sync {
    fn inc_total_by(&self, total: usize);
    fn inc_free_item_by(&self, free: usize);
    fn dec_free_item(&self);

    fn total_item(&self) -> Option<usize>;
    fn free_item(&self) -> Option<usize>;
}

/// Memory allocation is:
///
/// ```text
///     |-- PageHeader --| -- MAYBE PADDING -- |-- Node<T> ---- ... ->
/// ```
struct PageHeader<T> {
    owner: NonNull<dyn PoolInner<T>>,

    /// Original buffer, **_contains_** `self` at start.
    raw_buffer: NonNull<[MaybeUninit<Slot<T>>]>,

    /// `raw_buffer[payload_start_index..]` is content.
    payload_start_index: u32,

    /// Only referred during entire pool destruction. When it reaches == `page_length`, the
    /// entire page will be deallocated.
    dealloc_counter: u32,
}

// ==== Pool Logic ====

impl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock> PoolInner<T>
    for PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
where
    T: 'static,
    CreateFn: FnCreate<T>,
    PrepareFn: FnApply<T>,
    CleanFn: FnApply<T>,
    Cnt: Counter,
    AllocLock: PageLock,
{
    fn checkout_sync(&self) -> NonNull<Slot<T>> {
        loop {
            // When *sync-mode* references are returned to `free_head_may_weak` with any remaining
            // weak references alive, and if the pool is also used with *local-mode* references that
            // only search for references in the `free_head` stack, there can be a starvation issue.
            // This happens because *sync-mode* references, when checked in with an alive weak
            // reference, continuously consume and return slots to `free_head_may_weak`. As a
            // result, local-mode checkouts might suffer from a lack of available references in
            // `free_head`.
            //
            // To prevent this situation, even if the user doesn't create any weak sync references,
            // (as there's no cheap way to check if really weak sync is not used) we prioritize
            // checking the weak stack first for *sync-mode* checkouts.
            //
            // SAFETY:
            //   * Access to `free_head` is exclusive as long as it's locked.
            //   * Access to `free_head_may_weak` is possibly shared between "already expired" weak
            //     references, however, they are guaranteed to not elevate/interfere slot jobs
            unsafe {
                if let Some(slot) = try_pop_slot(&self.free_head_may_weak) {
                    self.mark_slot_checkout(slot, true);
                    break slot;
                }

                // If there are no available references in the weak stack, we then check all the
                // stacks.
                if let Some(slot) = try_pop_slot(&self.free_head) {
                    self.mark_slot_checkout(slot, false);
                    break slot;
                }
            }

            // No slots are available here; additional pages need to be allocated.
            self.expand_by_default();
        }
    }

    fn checkout_local(&self) -> NonNull<Slot<T>> {
        loop {
            // In local case, we don't care whether there's weak reference or not. This is
            // because local reference is only released when both of strong and weak reference
            // are released.
            //
            // SAFETY: Same as above.
            if let Some(slot) = unsafe { try_pop_slot(&self.free_head) } {
                self.mark_slot_checkout_local(slot);
                break slot;
            }

            // It's completely same routine with checkout().
            self.expand_by_default();
        }
    }

    fn allocate_page(&self, page_size: Option<NonZeroUsize>) {
        // It does not lock for intent; since page allocation occurs due to explicit user
        // request, it does not need to be bottlenecked.
        self.allocate_page_impl(page_size);
    }

    fn num_total_items(&self) -> Option<usize> {
        self.item_counter.total_item()
    }

    fn num_free_items(&self) -> Option<usize> {
        self.item_counter.free_item()
    }

    fn sync_slot_cleanup_then_checkin(&self, slot_ref: &mut Slot<T>) {
        self.item_counter.inc_free_item_by(1);

        debug_assert!(unsafe { slot_ref.atomic_strong().load(Ordering::Relaxed) == 0 });

        // Check if this is the sole reference remaining including entire weak references.
        let last_weak_ref = unsafe { slot_ref.atomic_weak() }.fetch_sub(1, Ordering::Acquire) == 1;

        if last_weak_ref {
            // If this is last weak reference; reset generation value to 0. This will reduce
            // possibility of generation overflow.
            slot_ref.generation.store(0, Ordering::Release);
        } else {
            // If there's any alive weak reference, increment generation as early as possible. This
            // expires every other weak references referring to this version of strong reference.
            slot_ref.generation.fetch_add(1, Ordering::Release);
        }

        // Will increment generation by 1 if it has any alive weak reference(except this).
        // Otherwise, generation is reset to 0 and pushed to total free list.

        // Cleanup inner data
        self.clean_func.call(&mut slot_ref.value);

        if !last_weak_ref {
            // put it back to free_head_with_ref
            push_slot(&self.free_head_may_weak, slot_ref.into());
        } else {
            // put it back to free_head
            push_slot(&self.free_head, slot_ref.into());

            self.sync_slot_dispose(slot_ref);
        }

        // NOTE: EXTRA CAUTION HERE; since THIS line, any interaction with `self` or `slot_ref` must
        // not occured anymore since it'll dispose `self` inside if this was the last reference to
        // the pool, which may invalidate all the references that we're accessing from here.
    }

    fn local_slot_cleanup(&self, slot_ref: &mut Slot<T>) {
        self.item_counter.inc_free_item_by(1);

        // TODO: Sync memory barrier of weak, strong count.

        todo!()
    }

    fn sync_slot_dispose(&self, _slot_ref: &mut Slot<T>) {
        // It could be disposed during it's still inside of the free queue list. Therefore, we can't
        // assert that any of strong and weak reference count would be zero.
        //
        //      debug_assert!(unsafe { slot_ref.atomic_strong().load(Ordering::Relaxed) == 0 });
        //      debug_assert!(unsafe { slot_ref.atomic_weak().load(Ordering::Relaxed) == 0 });
        //
        // Therefore, the only thing that we have to do here is just decrementing reference count of
        // self. This may drop the entire pool if it was the last reference.

        // SAFETY: self is originally was `Arc`
        drop(unsafe { Arc::from_raw(self as *const _) });
    }

    fn local_slot_checkin_then_dispose(&self, slot_ref: &mut Slot<T>) {
        // TODO: Decrement self's reference count.

        // Prepare to put this node to free stack.

        todo!()
    }
}

/// Tries to pop the foremost slot from the given head socket. it'll return [`None`] when it
/// eventually fails since there's no more elements to pop.
unsafe fn try_pop_slot<T>(head: &Mutex<*mut Slot<T>>) -> Option<NonNull<Slot<T>>> {
    let mut head = head.lock();

    let new_head = head.as_mut()?.next_free;
    let popped = replace(&mut *head, new_head);

    drop(head); // Drops lock early as possible.
    (*popped).next_free = null_mut();

    Some(NonNull::new_unchecked(popped))
}

fn push_slot<T>(head: &Mutex<*mut Slot<T>>, mut slot: NonNull<Slot<T>>) {
    // TEMPORARY

    // unsafe {
    //     slot.as_mut().next_free = *head.data_ptr();
    //     (*head.data_ptr()) = slot.as_ptr();

    //     return;
    // }

    let mut head = head.lock();

    // Next element MUST be free
    debug_assert!(unsafe { slot.as_ref() }.next_free.is_null());

    unsafe { slot.as_mut() }.next_free = *head;

    *head = slot.as_ptr();
}

impl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
    PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
where
    T: 'static,
    CreateFn: FnCreate<T>,
    PrepareFn: FnApply<T>,
    CleanFn: FnApply<T>,
    Cnt: Counter,
    AllocLock: PageLock,
{
    fn mark_slot_checkout(&self, mut p_slot: NonNull<Slot<T>>, has_weak: bool) {
        self.item_counter.dec_free_item();

        // In this context, we have exclusive *STRONG* access to this value.

        let slot = unsafe { p_slot.as_mut() };

        // If it has weak count, we can't guarantee that it's larger than 0. However, in
        // opposite case, the weak count and the generation MUST be zero.
        debug_assert!(
            has_weak || (slot.weak_count == 0 && slot.generation.load(Ordering::Relaxed) == 0)
        );

        // SAFETY: `weak_count` is guaranteed accessed as atomic as long as `has_weak` is true.
        let no_alive_weak_ref =
            !has_weak || (unsafe { slot.atomic_weak().fetch_add(1, Ordering::Acquire) } == 0);
        //                ^^^ `has_weak` set to true if we fetched this entity from
        //                `free_head_may_weak`, however, as its name implies, the dangling weak
        //                reference possibly be resolved while it is free. Therefore, it's better to
        //                double-check if this reference actually has *weak count* as advertised.

        if no_alive_weak_ref {
            // We have exclusive
            slot.generation = AtomicU32::new(1);
            slot.weak_count = 1; // NOTE: See implementation of `Arc`
            slot.strong_count = 1;

            // SAFETY: self is dereference of `Arc<Self>`.
            // - Additionaly, it is guaranteed that `Arc<Self>` is always valid, since we're calling
            //   THIS method thorugh the valid `Arc<Self>` reference!
            unsafe { Arc::increment_strong_count(self) }
        } else {
            // Let expired weak count observe new generation value before we modifying strong count.
            //
            //      slot.generation.fetch_add(1, Ordering::AcqRel);
            //
            // NOTE: removing above code; as generation value is better to be incremented in checkin
            // side to notify weak handles expiration as soon as possible, to not make pointless
            // weak references repeatedly.

            // We need to access the strong count atomically, since the expired weak reference would
            // try upgrading (even it's invalid) to strong reference
            unsafe { slot.atomic_strong() }.store(1, Ordering::Relaxed);

            // We don't increment reference count of `self` here; since previous weak reference
            // count was non-zero, which means the previous strong count increment is still
            // remaining thus incrementing it again will leak the self reference forever.
        }

        // Now data is valid to access; prepare the data
        self.prepare_func.call(&mut slot.value);
    }

    fn mark_slot_checkout_local(&self, mut p_slot: NonNull<Slot<T>>) {
        self.item_counter.dec_free_item();

        // In this context, we have exclusive access to this value. And it is safe to deal with
        // this value locally since we're currently exclusively owning this slot!

        let slot = unsafe { p_slot.as_mut() };
        debug_assert!(slot.weak_count == 0 && slot.generation.load(Ordering::Relaxed) == 0);

        // When the last strong reference dies, it decrements weak reference count either.
        // Despawning the slot itself is the role of last weak reference.
        Slot::add_ref_local(p_slot);
        Slot::weak_add_ref_local(p_slot);

        // SAFETY: self is dereference of `Arc<Self>`
        unsafe { Arc::increment_strong_count(self) };

        // Now data is valid to access; prepare the data
        self.prepare_func.call(&mut slot.value);
    }

    fn expand_by_default(&self) {
        if let Some(_job) = self.alloc_lock.try_acquire_job() {
            self.allocate_page_impl(None);
        } else {
            // Wait for another thread that has acquired the job handle to complete its
            // work.
            self.alloc_lock.acquire_job();
        }
    }

    /// Actual allocation logic
    fn allocate_page_impl(&self, page_size: Option<NonZeroUsize>) {
        let elem_count = page_size.unwrap_or(self.fallback_page_size).get();
        let slot_size = size_of::<Slot<T>>();

        // Offset page payload to write page header contents in it.
        let payload_offset = (size_of::<PageHeader<T>>() + slot_size - 1) / slot_size;
        let alloc_count = payload_offset + elem_count;

        // Alignment of `Slot` must be larger than `PageHeader`. This is ALWAYS true as long as
        // following assertion is satisfied; as `PageHeader` never aligned to other than pointer
        // size.
        macro_rules! check_align_size {
            ($t:ty) => {
                static_assertions::const_assert!(
                    std::mem::align_of::<PageHeader<$t>>() <= std::mem::align_of::<Slot<$t>>()
                )
            };
        }

        check_align_size!(());
        check_align_size!(u8);
        check_align_size!(u16);
        check_align_size!(u32);
        check_align_size!(u64);
        check_align_size!(u128);

        let buffer = {
            let mut v = Vec::<MaybeUninit<Slot<T>>>::new();
            v.reserve_exact(alloc_count);

            // SAFETY:
            // 1. capacity is exactly `alloc_count`
            // 2. `MaybeUninit` is zeroable type.
            unsafe { v.set_len(alloc_count) };

            v.into_boxed_slice()
        };

        // SAFETY: We've just initialized this buffer
        let mut raw_buffer = unsafe { NonNull::new_unchecked(Box::into_raw(buffer)) };
        let self_dyn: &dyn PoolInner<T> = self;

        let head = PageHeader {
            // SAFETY: We'll never mutably access owner.
            owner: unsafe { NonNull::new_unchecked(transmute(self_dyn)) },
            raw_buffer,
            payload_start_index: payload_offset as _,
            dealloc_counter: elem_count as _,
        };

        // SAFETY: 1. Space allocated enough, 2. Init by none yet.
        unsafe { (raw_buffer.as_ptr() as *mut PageHeader<T>).write(head) }

        // Initialize payload elements ...
        let payload_slice = &mut unsafe { raw_buffer.as_mut() }[payload_offset..];

        for (index, slot_ref) in payload_slice.iter_mut().enumerate() {
            let slot_ptr = slot_ref as *mut MaybeUninit<Slot<T>>;
            let slot_value = Slot::<T> {
                value: self.init_func.call(), // TODO: Check panic behavior

                // SAFETY:
                // - For 0..end-1 elems, its not yet initialized, but we'll.
                // - For last element which points to invalid memory space, will be handled
                //   after breaking out of this loop.
                next_free: unsafe { transmute(slot_ptr.add(1)) },

                generation: AtomicU32::new(0),
                strong_count: 0,
                weak_count: 0,

                // From each slots, stepping back for this amount will point to `PageHeader`
                index_offset: (index + payload_offset) as _,
            };

            // SAFETY: `slot_ptr` points to valid memory.
            unsafe { (*slot_ptr).write(slot_value) };
        }

        // This is important part ...
        // - Last element's `next_free`, MUST point to actually valid argument.
        // - And this step MUST not interfere `checkin` operations from different threads.

        // SAFETY: 1. Initialized, 2. Payload array length never be zero.
        let (first_ptr, last_elem) = unsafe {
            (
                payload_slice
                    .first_mut()
                    .unwrap_unchecked()
                    .assume_init_mut() as *mut _,
                payload_slice
                    .last_mut()
                    .unwrap_unchecked()
                    .assume_init_mut(),
            )
        };

        // Preemptively increment both the total and free counts here. It's particularly
        // important to increment the free count before inserting a new page into the stack, as
        // failing to do so could reduce the free count below zero, potentially causing a panic
        // or similar issue.
        //
        // Given that users may not expect an exact status for the free count in a multithreaded
        // environment, adjusting the values here is unlikely to cause any issues.
        self.item_counter.inc_total_by(elem_count);
        self.item_counter.inc_free_item_by(elem_count);

        // Prepend the whole page allocation to existing free head stack.
        let mut free_head = self.free_head.lock();
        last_elem.next_free = *free_head;
        *free_head = first_ptr;
    }
}

// ==== Drop guard of Pool ====

impl<T, CreateFn, PrepareFn, CleanFn, Counter, AllocLock> Drop
    for PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Counter, AllocLock>
{
    fn drop(&mut self) {
        // In this context, EVERY strong reference to the pool is dropped. This indicates:
        //
        // - Every handles to `Pool<T>` was dropped.
        // - Every slots of EVERY page was freed.
        // - Plus, EVERY WEAK reference to each slot was freed. (important!)
        //   - The pool reference is only released when both strong and weak reference dropped
        //     to zero, which means, the pool itself is never dropped as long as a single weak
        //     reference to an item inside
        //
        // Therefore, we can safely assume that this is the only thread which accesses every
        // element of all items

        let track_release_fn = |mut slot: *mut Slot<T>| unsafe {
            while !slot.is_null() {
                // First retrieve owning page header and next node of this slot.
                let head = Slot::get_header_ptr(slot);
                let next = (*slot).next_free;

                debug_assert!((*slot).strong_count == 0);
                debug_assert!((*slot).weak_count == 0);
                debug_assert!((*slot).generation.load(Ordering::Relaxed) == 0);

                // Then manually destroy the slot since it was originally `MaybeUnitit`.
                slot.drop_in_place();

                // Then, decrement deallocation counter of the page header.
                (*head).dealloc_counter -= 1;

                if (*head).dealloc_counter == 0 {
                    // We can safely dispose this page, since all of the node included in this page
                    // was deallocated.

                    let raw_buffer = (*head).raw_buffer;
                    head.drop_in_place();

                    // Finally, we need to deallocate the buffer
                    drop(Box::from_raw(raw_buffer.as_ptr()))
                }

                slot = next;
            }
        };

        track_release_fn(*self.free_head.lock());
        track_release_fn(*self.free_head_may_weak.lock());
    }
}

// ========================================================== Slot Logics ===|

/// A container for single value.
#[repr(C)] // Slot can directly be converted from the address of value `T`.
pub(crate) struct Slot<T> {
    value: T,

    /// Nearlest free item that this slot is pointing to.
    next_free: *mut Slot<T>,

    /// # Concept of Generation and Weak Count
    ///
    /// To enable the coexistence of expired weak references with new allocations in the same slot,
    /// a generation value is introduced, tied to the strong count. The strong reference operates as
    /// usual (atomically adding/removing reference count, as long as the total number of strong
    /// counts is less than 2^32-1). However, the weak reference's upgrade operation differs from
    /// the normal [`std::sync::Arc`] behavior.
    ///
    /// Once all strong references to a slot expire, a weak reference can no longer upgrade its
    /// reference since the strong reference count is 0, regardless of its generation.
    ///
    /// Then, with every new allocation of a slot, the generation value is incremented by 1 before
    /// increasing its strong reference count. Subsequently, any upgrade request from a weak
    /// reference will be rejected if the generation values mismatch, even if the strong count is
    /// non-zero.
    ///
    /// This method allows for the safe reuse of memory blocks held by alive weak references.
    ///
    /// # Warning
    ///
    /// There is a single caveat to be aware of: With every 2^32 reallocations of the same slot, the
    /// generation value may cycle, potentially validating the dead weak references of existing
    /// handles.
    ///
    /// These might be silently upgraded to valid strong references, which is likely unintended.
    ///
    /// XXX: Should we consider using 64-bit generation ID? This would increase the default memory
    /// overhead to 32.
    ///
    /// ---
    ///
    /// In the case of local references, generation is not a concern since a local reference is only
    /// released when both strong and weak references are freed. This approach is adopted because
    /// even if a reference is local, it can potentially be checked out to another thread, where it
    /// remains local. In such scenarios, two different threads may naively manipulate the same weak
    /// reference count in a non-atomic manner.
    ///
    /// Implementing every weak count operation to support the local, atomic case may seem
    /// excessive. (To ensure robust behavior in this context, we might need to use thread-local
    /// storage or a similar mechanism, considering that the pool itself operates in a
    /// multi-threaded environment)
    ///
    generation: AtomicU32,
    strong_count: u32,
    weak_count: u32,

    /// An index offset from start of the byte buffers. As a consequence, single page size must
    /// not exceed 2^16 args.
    index_offset: u32,
}

impl<T: 'static> Slot<T> {
    pub unsafe fn atomic_strong(&self) -> &AtomicU32 {
        AtomicU32::from_ptr(&self.strong_count as *const _ as _)
    }

    pub unsafe fn atomic_weak(&self) -> &AtomicU32 {
        AtomicU32::from_ptr(&self.weak_count as *const _ as _)
    }

    // ==== Local API ====
    #[inline]
    pub fn add_ref_local(mut this: NonNull<Self>) {
        let this = Self::access_mut(&mut this);
        this.strong_count += 1;

        // It's only 32-bit reference count, its value can overflow in feasible time.
        assert!(this.strong_count < u32::MAX);
    }

    #[inline]
    pub fn release_local(p_this: NonNull<Self>) {
        let mut p_this_b = p_this; // Just workaround to avoid borrow checker complaint
        let this = Self::access_mut(&mut p_this_b);

        this.strong_count -= 1;
        if this.strong_count > 0 {
            return;
        }

        // In local mode, strong reference disposal only cleans up the slot, not freeing.
        this.owner()
            .local_slot_cleanup(Self::access_mut(&mut { p_this }));

        // Decrement single weak reference initially incurred by strong references.
        Self::weak_release_local(p_this);
    }

    #[inline]
    pub fn weak_add_ref_local(mut this: NonNull<Self>) {
        let this = Self::access_mut(&mut this);
        this.weak_count += 1;

        assert!(this.weak_count < u32::MAX);
    }

    #[inline]
    pub fn weak_release_local(p_this: NonNull<Self>) {
        let mut p_this_b = p_this; // Just workaround to avoid borrow checker complaint
        let this = Self::access_mut(&mut p_this_b);

        this.weak_count -= 1;
        if this.weak_count > 0 {
            return;
        }

        this.owner()
            .local_slot_checkin_then_dispose(Self::access_mut(&mut { p_this }));

        // NOTE: There MUST be no more subsequent interaction with `this` or `this_ptr` here since
        // it will remove the owner's reference if it was the last reference that was holding the
        // owner, which invalidates EVERY data related to this method.
    }

    pub fn try_upgrade_local(this_ptr: NonNull<Self>) -> Option<NonNull<Self>> {
        todo!()
    }

    pub fn downgrade_local(this_ptr: NonNull<Self>) {
        todo!()
    }

    // ========================================================== Sync API ===|

    #[inline]
    pub fn add_ref(this: NonNull<Self>)
    where
        T: Send + Sync,
    {
        // It's enough with relaxed ordering here:
        // - If it's the thread that created this variable, since it's local, it's synchronized
        //   already.
        // - It never get expired during adding refcnt, since the caller of 'add_ref' is already
        //   holding at least one strong reference.
        //
        // SAFETY: This is never called by local mode handles.
        unsafe {
            Self::access(&this)
                .atomic_strong()
                .fetch_add(1, Ordering::Relaxed);
        }
    }

    #[inline]
    pub fn release(this_ptr: NonNull<Self>) {
        let mut this_ptr_b = this_ptr; // Just workaround to avoid borrow checker complaint
        let this = Self::access(&this_ptr);
        let prev_strong = unsafe { this.atomic_strong() }.fetch_sub(1, Ordering::Release);

        if prev_strong > 1 {
            // We're not the last reference.
            return;
        }

        debug_assert!(prev_strong != 0, "what?");

        // Since we're the last reference and observed that strong count is zero, it's guaranteed
        // that no other weak reference can upgrade this handle to valid strong reference.

        // In sync mode, slot is checked in even if there's alive weak handles out there.
        this.owner()
            .sync_slot_cleanup_then_checkin(Self::access_mut(&mut this_ptr_b));
    }

    /// Adding ref does not care whether
    pub fn try_clone_weak(this_ptr: NonNull<Self>, gen: u32) -> Option<NonNull<Self>> {
        let this = Self::access(&this_ptr);

        // The weak reference MUST present at least one for `this` reference.
        debug_assert!(unsafe { this.atomic_weak() }.load(Ordering::Acquire) >= 1);

        // Check if this is already expired. `Acquired` oredering required here to observe
        // generation value increment by concurrent `release` operation.
        if this.generation.load(Ordering::Acquire) != gen {
            // When generation mismatches, we don't create weak reference from this anymore.
            return None;
        }

        // After the above check, it's possible that the generation might change. However, this
        // doesn't require strict verification, as the generation is rigorously validated during an
        // actual upgrade. This approach is justified because:
        //
        // - The slot is not returned to the `free_head` as long as any weak references are present.
        // - Therefore, the generation value only increases incrementally.
        // - For example, encountering the same generation value again is unlikely unless it cycles
        //   back. While this is rare (given it's bound to a 32-bit limit), the possibility remains
        //   in cases of leaked or hidden weak references persisting throughout the application's
        //   lifetime.
        // - Generation rotation isn't a concern as long as an upgrade doesn't occur at the precise
        //   moment of rotation. This is an expected behavior, as the upgraded reference is still a
        //   valid object. Thus, users can prevent conflicts by implementing a detection
        //   mechanism...
        //   - XXX: However, obligating users to enhance the detection mechanism could be
        //     counterproductive.
        //   - A practical solution could be to use a 64-bit generation ID, which would add an extra
        //     4 bytes of memory overhead per slot allocation; increasing it to 28. TODO: Review
        //     this.

        unsafe { this.atomic_weak() }.fetch_add(1, Ordering::Release);

        // Therefore, now we just regard that this weak reference is valid enough.
        Some(this_ptr)
    }

    pub fn weak_release(mut this_ptr: NonNull<Self>) {
        let this = Self::access_mut(&mut this_ptr);

        // Decrement weak reference count. If it's not zero, it's just okay to return.
        let prev_weak = unsafe { this.atomic_weak() }.fetch_sub(1, Ordering::Release);

        if prev_weak > 1 {
            return;
        }

        // This represents the last weak reference. Given that the count never drops to zero as long as there is
        // any strong reference present, it can be concluded that at this point, no strong references are alive.
        debug_assert!(unsafe { this.atomic_strong() }.load(Ordering::Acquire) == 0);

        // Now we can safely dispose this slot.
        this.owner().sync_slot_dispose(this);

        // NOTE: There MUST be no more subsequent interaction with `this` or `this_ptr` here since
        // it will remove the owner's reference if it was the last reference that was holding the
        // owner, which invalidates EVERY data related to this method.
    }

    pub fn try_upgrade(this_ptr: NonNull<Self>, gen: u32) -> Option<NonNull<Self>> {
        // 1. Check if strong-count is nonzero
        // 2. Create upgraded reference preemptively
        // 3. Check generation is valid
        //   3. 1. Drops if it was invalid generation
        //
        // It's just okay to create falsy strong reference since:
        // - As long as there's alive weak reference, the generation will keep incrementing; i.e.
        //   won't collide practically in short-term.
        // - Regardless if it's same reference that was originally subscribing or not, cloning
        //   existing reference is defined operation, and disposing it is defined either. Even at
        //   worst case, it's just checking out object from different thread, which is valid
        //   operation as long as the user used the pool in safe way.

        let this = Self::access(&this_ptr);
        let strong_count = unsafe { this.atomic_strong() };

        // We need to repeat since other thread may intercept our trial to increment strong count in
        // non-intrusive manner.

        fn check_incr_fn(strong: u32) -> Option<u32> {
            if strong == 0 {
                return None;
            }

            // Just check if it doesn't overflow.
            assert!(strong < u32::MAX);

            Some(strong + 1)
        }

        if strong_count
            .fetch_update(Ordering::Release, Ordering::Relaxed, check_incr_fn)
            .is_err()
        {
            // It simply failed to upgrade to valid strong reference.
            return None;
        }

        // Now we have valid strong reference. Check if generation is valid.

        if this.generation.load(Ordering::Acquire) != gen {
            // Since we've upgraded wrong reference, release it.
            // - In most cases, it'll just decrement the strong reference count of slot.
            // - At some edge case, this release would checkin the slot as last strong reference,
            //   which is just okay since it never exits sync mode as long as there's remaining weak
            //   reference.
            Self::release(this_ptr);
            None
        } else {
            // Okay, we've got valid strong reference. Return it to user.
            Some(this_ptr)
        }
    }

    /// Returns generation
    pub fn downgrade(this_ptr: NonNull<Self>) -> u32 {
        let this = Self::access(&this_ptr);

        // Add weak reference.
        unsafe { this.atomic_weak() }.fetch_add(1, Ordering::Relaxed);

        // Before releasing strong reference, retrive current generation value.
        this.generation.load(Ordering::Relaxed)
    }

    pub fn try_mut<'a>(this_ptr: NonNull<Self>) -> Option<&'a mut T> {
        let this = Self::access(&this_ptr);

        // To return mutable reference correctly, we need to check if it's truly unique reference.
        unsafe {
            (this.atomic_strong().load(Ordering::Relaxed) == 1
                && this.atomic_weak().load(Ordering::Relaxed) == 1)
                .then(|| &mut (*this_ptr.as_ptr()).value)
        }
    }

    // ==== Accessors ====

    #[inline]
    fn access(this: &NonNull<Self>) -> &Self {
        // SAFETY: using with caution 🤔
        unsafe { this.as_ref() }
    }

    #[inline]
    fn access_mut(this: &mut NonNull<Self>) -> &mut Self {
        // SAFETY: using with caution 🤔
        unsafe { this.as_mut() }
    }

    fn owner(&self) -> &'static dyn PoolInner<T> {
        let this_addr = self as *const _ as *const MaybeUninit<Self>;
        let header_addr = unsafe { this_addr.sub(self.index_offset as _) };

        debug_assert!(self.index_offset >= 1);

        // SAFETY: index_offset is set on slot init, and never get changed over time.
        let header = unsafe { &*(header_addr as *const PageHeader<T>) };

        // SAFETY: as long as we can access any slot, the owner reference never dangle.
        unsafe { header.owner.as_ref() }
    }

    pub fn get_owner_arc(this: NonNull<Self>) -> Arc<dyn PoolInner<T>> {
        let this = Self::access(&this);

        unsafe { Arc::from_raw(this.owner()) }.clone()
        // 										   ^^^ `from_raw` won't increment strong ref!
    }
}

impl<T> Slot<T> {
    unsafe fn get_header_ptr(this: *mut Self) -> *mut PageHeader<T> {
        let index_offset = (*this).index_offset;
        (this as *mut MaybeUninit<Self>).sub(index_offset as _) as _
    }
}
