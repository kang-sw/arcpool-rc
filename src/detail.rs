use std::{
    mem::{replace, size_of, transmute, MaybeUninit},
    num::NonZeroUsize,
    ptr::{null_mut, NonNull},
    sync::{
        atomic::{self, AtomicU32, Ordering},
        Arc,
    },
};

use parking_lot::Mutex;

pub(crate) mod pool {
    #[derive(Default)]
    pub struct Builder<T, CreateFn, PrepareFn, CleanFn> {
        _marker_ty: std::marker::PhantomData<T>,
        page_size: usize,
        init_func: CreateFn,
        prepare_func: PrepareFn,
        clean_func: CleanFn,
        use_page_alloc_lock: bool,
    }

    // ==== Builder Component: Cleaner Function ====

    impl<T> super::ApplyFunc<T> for () {
        fn call(&self, _: &mut T) {}
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
}

pub(crate) trait PoolInner<T>: Send + Sync + 'static {
    fn checkout(&self) -> NonNull<Slot<T>>;
    fn checkout_local(&self) -> NonNull<Slot<T>>;

    fn allocate_page(&self, page_size: Option<NonZeroUsize>);

    fn total_item(&self) -> Option<usize>;
    fn free_item(&self) -> Option<usize>;

    fn checkin(&self, ptr: NonNull<Slot<T>>);
    fn checkin_local(&self, ptr: NonNull<Slot<T>>);
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
    free_head: Mutex<*mut Slot<T>>,

    /// If only the strong reference was released (in sync) (i.e. any weak reference presents),
    /// the node will be stored here. Only `sync` checkouts are allowed to access this storage,
    /// as the generation based hot reuse is exclusively permitted for atomic versions.
    free_head_may_weak: Mutex<*mut Slot<T>>,

    fallback_page_size: NonZeroUsize,

    init_func: CreateFn,
    prepare_func: PrepareFn,
    clean_func: CleanFn,

    alloc_lock: AllocLock,

    item_counter: Counter,
}

unsafe impl<T1, T2, T3, T4, T5, T6> Send for PoolInnerImpl<T1, T2, T3, T4, T5, T6> {}
unsafe impl<T1, T2, T3, T4, T5, T6> Sync for PoolInnerImpl<T1, T2, T3, T4, T5, T6> {}

trait ApplyFunc<T>: 'static + Send + Sync {
    fn call(&self, _: &mut T);
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
    fn dec_free_item_by(&self, free: usize);

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

    /// `raw_buffer[payload_start_at..]` is content.
    payload_start_at: u32,

    /// Only referred during entire pool destruction. When it reaches == `page_length`, the
    /// entire page will be deallocated.
    dealloc_counter: u32,
}

// ==== Pool Logic ====

impl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock> PoolInner<T>
    for PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
where
    T: 'static,
    CreateFn: Fn() -> T + Send + Sync + 'static,
    PrepareFn: ApplyFunc<T>,
    CleanFn: ApplyFunc<T>,
    Cnt: Counter,
    AllocLock: PageLock,
{
    fn checkout(&self) -> NonNull<Slot<T>> {
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

    fn total_item(&self) -> Option<usize> {
        self.item_counter.total_item()
    }

    fn free_item(&self) -> Option<usize> {
        self.item_counter.free_item()
    }

    fn checkin(&self, ptr: NonNull<Slot<T>>) {
        // TODO: Decrement self's reference count.

        todo!()
    }

    fn checkin_local(&self, ptr: NonNull<Slot<T>>) {
        // TODO: Sync memory barrier of weak, strong count.

        // TODO: Decrement self's reference count.

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
    CreateFn: Fn() -> T + Send + Sync + 'static,
    PrepareFn: ApplyFunc<T>,
    CleanFn: ApplyFunc<T>,
    Cnt: Counter,
    AllocLock: PageLock,
{
    fn mark_slot_checkout(&self, mut p_slot: NonNull<Slot<T>>, has_weak: bool) {
        // In this context, we have exclusive *STRONG* access to this value.

        let slot = unsafe { p_slot.as_mut() };

        // If it has weak count, we can't guarantee that it's larger than 0. However, in
        // opposite case, the weak count and the generation MUST be zero.
        debug_assert!(
            has_weak || (slot.weak_count == 0 && slot.generation.load(Ordering::Relaxed) == 0)
        );

        // Before giving it a strong reference count, increment generation by 1 whether it has weak
        // reference or not. (it'll be 1 if there was no weak references)
        //
        // Memory order should be `release`, since if any expired weak reference present and it
        // observes the strong reference count existance before the generation value change is
        // observed, it will be upgraded to invalid strong reference.

        // SAFETY: `weak_count` is guaranteed accessed as atomic as long as `has_weak` is true.
        let no_alive_weak_ref =
            !has_weak || (unsafe { slot.as_atomic_weak().fetch_add(1, Ordering::Acquire) } == 0);
        //                ^^^ `has_weak` set to true if we fetched this entity from
        //                `free_head_may_weak`, however, as its name implies, the dangling weak
        //                reference possibly be resolved while it is free. Therefore, it's better to
        //                double-check if this reference actually *has weak* count as advertised.

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
            slot.generation.fetch_add(1, Ordering::AcqRel);
            slot.strong_count = 1; // It's okay to accessing it via non-atomic way, as the expired
                                   // weak reference won't care the strong count value if generation
                                   // value mismatches. Therefore the only guarantee that we should
                                   // provide is generation is modified *before* strong count become
                                   // any non-zero value, which is accomplished by `AcqRel` ordering

            // We don't increment reference count of `self` here; since previous weak reference
            // count was non-zero, which means the previous strong count increment is still
            // remaining thus incrementing it again will leak the self reference forever.
        }

        // Now data is valid to access; prepare the data
        self.prepare_func.call(&mut slot.value);
    }

    fn mark_slot_checkout_local(&self, mut p_slot: NonNull<Slot<T>>) {
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
            // TODO: Move this to the doc comment of builder.

            // Acquiring this lock isn't mandatory for page allocation, but it's
            // recommended. The allocation process involves executing user-provided
            // initialization logic, which can have unpredictable execution time.
            //
            // Without the lock, multiple threads might concurrently see empty free element
            // stacks and overallocate pages. Although this results in excessive memory
            // allocation, all 'extra' allocations will be added to the free list
            // effectively. Moreover, the user-provided initialization logic will run
            // concurrently in this scenario. Thus, disabling the allocation lock can be a
            // valid policy if extensive capacity expansion is preferred.
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
            payload_start_at: payload_offset as _,
            dealloc_counter: elem_count as _,
        };

        // SAFETY: 1. Space allocated enough, 2. Init by none yet.
        unsafe { (raw_buffer.as_ptr() as *mut PageHeader<T>).write(head) }

        // Initialize payload elements ...
        let payload_slice = &mut unsafe { raw_buffer.as_mut() }[payload_offset..];

        for (index, slot_ref) in payload_slice.iter_mut().enumerate() {
            let slot_ptr = slot_ref as *mut MaybeUninit<Slot<T>>;
            let slot_value = Slot::<T> {
                value: (self.init_func)(), // TODO: Check panic behavior

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
        // TODO

        // In this context, EVERY strong reference to pool is dropped. This indicates:
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

        todo!()
    }
}

// ========================================================== Slot Logics ===|

/// A container for single value.
pub(crate) struct Slot<T> {
    value: T,
    next_free: *mut Slot<T>,

    /// # Concept of Generation and Weak Count
    ///
    /// To enable the coexistence of expired weak references with new allocations in the same
    /// slot, a generation value is introduced, tied to the strong count. The strong reference
    /// operates as usual (atomically adding/removing reference count, as long as the total
    /// number of strong counts is less than 2^32-1). However, the weak reference's upgrade
    /// operation differs from the normal [`std::sync::Arc`] behavior.
    ///
    /// Once all strong references to a slot expire, a weak reference can no longer upgrade its
    /// reference since the strong reference count is 0, regardless of its generation.
    ///
    /// Then, with every new allocation of a slot, the generation value is incremented by 1
    /// before increasing its strong reference count. Subsequently, any upgrade request from a
    /// weak reference will be rejected if the generation values mismatch, even if the strong
    /// count is non-zero.
    ///
    /// This method allows for the safe reuse of memory blocks held by alive weak references.
    ///
    /// # Warning
    ///
    /// There is a single caveat to be aware of: With every 2^32 reallocations of the same slot,
    /// the generation value may cycle, potentially validating the dead weak references of
    /// existing handles.
    ///
    /// These might be silently upgraded to valid strong references, which is likely unintended.
    ///
    /// XXX: Should we consider a 64-bit generation ID? This would increase the default memory
    /// overhead to 32.
    ///
    /// ---
    ///
    /// In local case, it does not care generation as local reference is only released when both
    /// of strong and weak reference are freed. This is since we can't guarantee that
    generation: AtomicU32,
    strong_count: u32,
    weak_count: u32,

    /// An index offset from start of the byte buffers. As a consequence, single page size must
    /// not exceed 2^16 args.
    index_offset: u32,
}

impl<T> Slot<T> {
    pub unsafe fn as_atomic_strong(&mut self) -> &AtomicU32 {
        AtomicU32::from_ptr(&mut self.strong_count)
    }

    pub unsafe fn as_atomic_weak(&mut self) -> &AtomicU32 {
        AtomicU32::from_ptr(&mut self.weak_count)
    }

    // ==== Local API ====
    pub fn add_ref_local(this: NonNull<Self>) {
        todo!()
    }

    pub fn release_local(this: NonNull<Self>) {
        todo!()
    }

    pub fn weak_add_ref_local(this: NonNull<Self>) {
        todo!()
    }

    pub fn weak_release_local(this: NonNull<Self>, gen: u32) {
        todo!()
    }

    // ==== Sync API ====

    pub fn add_ref(this: NonNull<Self>) {
        todo!()
    }

    pub fn release(this: NonNull<Self>) {
        todo!()
    }

    /// Adding ref does not care whether
    pub fn weak_add_ref(this: NonNull<Self>) {
        todo!()
    }

    pub fn weak_release(this: NonNull<Self>, gen: u32) {
        todo!()
    }

    pub fn upgrade(this: NonNull<Self>, gen: u32) -> bool {
        todo!()
    }

    pub fn downgrade(this: NonNull<Self>) -> u32 {
        todo!()
    }

    fn header(&self) -> NonNull<PageHeader<T>> {
        todo!()
    }
}
