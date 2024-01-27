pub mod api {
    use std::{
        num::{NonZeroU16, NonZeroUsize},
        ptr::NonNull,
        sync::{Arc, Weak},
    };

    use crate::detail::{pool::Builder, PoolInner, Slot};

    #[derive(Clone)]
    pub struct Pool<T> {
        inner: Arc<dyn PoolInner<T>>,
    }

    #[derive(Clone)]
    pub struct WeakPool<T> {
        inner: Weak<dyn PoolInner<T>>,
    }

    impl<T> Pool<T>
    where
        T: 'static,
    {
        pub fn builder() -> Builder<T, (), (), ()> {
            todo!()
        }

        /// Allocate new item from pool. If no free slot presents, new page will be allocated.
        ///
        /// The returned item will automatically be checked in when dropped.
        pub fn checkout(&self) -> PoolItem<T>
        where
            T: Send + Sync,
        {
            PoolItem {
                slot: self.inner.checkout(),
            }
        }

        /// Allocate new item from pool as local object. It can hold non-send, non-sync object
        /// inside, and uses optimized intrinsics on cloning handles. (i.e. works as
        /// [`std::rc::Rc`] instead of [`std::sync::Arc`])
        pub fn checkout_local(&self) -> LocalPoolItem<T> {
            LocalPoolItem {
                slot: self.inner.checkout_local(),
            }
        }

        /// Allocate a single empty page (possibly with page_size). This method differs from methods
        /// like [`Vec::reserve`], which reserves *additional* elements based on the *currently
        /// used* items. In the default settings of the pool, since there's no awareness of the
        /// number of free item slots already prepared, this method simply allocates a new page and
        /// appends it to the linked list of free items.
        ///
        /// Therefore, if you use this method to 'reserve free space' repeatedly, similar to the
        /// approach in [`Vec`] families, it may result in continuously expanding memory usage.
        ///
        /// Number of
        pub fn allocate_page(&self, page_size: impl TryInto<NonZeroUsize>) {
            self.inner.allocate_page(page_size.try_into().ok());
        }
    }

    // ========================================================== Pool Item ===|

    pub struct PoolItem<T> {
        slot: NonNull<Slot<T>>,
    }

    pub struct WeakPoolItem<T> {
        slot: NonNull<Slot<T>>,
        gen: u32,
    }

    unsafe impl<T: Send + Sync> Send for PoolItem<T> {}
    unsafe impl<T: Send + Sync> Sync for PoolItem<T> {}
    unsafe impl<T: Send + Sync> Send for WeakPoolItem<T> {}
    unsafe impl<T: Send + Sync> Sync for WeakPoolItem<T> {}

    // ==== Impls ====

    impl<T: 'static + Send + Sync> PoolItem<T> {
        /// Tries to retrieve mutable reference of pulled object. It returns valid object only when
        /// the
        pub fn try_get_mut(&self) -> Option<&mut T> {
            todo!()
        }

        pub fn downgrade(&self) -> WeakPoolItem<T> {
            todo!()
        }
    }

    impl<T: 'static + Send + Sync> WeakPoolItem<T> {
        pub fn upgrade(&self) -> PoolItem<T> {
            todo!()
        }
    }

    impl<T: 'static + Send + Sync> Clone for PoolItem<T> {
        fn clone(&self) -> Self {
            todo!()
        }
    }

    impl<T: 'static + Send + Sync> Clone for WeakPoolItem<T> {
        fn clone(&self) -> Self {
            todo!()
        }
    }

    impl<T> Drop for PoolItem<T> {
        fn drop(&mut self) {
            todo!()
        }
    }

    impl<T> std::ops::Deref for PoolItem<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            todo!()
        }
    }

    impl<T> Drop for WeakPoolItem<T> {
        fn drop(&mut self) {
            Slot::release(self.slot)
        }
    }

    // ========================================================== Local Pool Item ===|

    /// Pool item for non-send items.
    pub struct LocalPoolItem<T> {
        slot: NonNull<Slot<T>>,
    }

    /// Pool item for non-weak items.
    pub struct WeakLocalPoolItem<T> {
        slot: NonNull<Slot<T>>,
        gen: u32,
    }

    // ========================================================== *Partial* API ===|

    // TODO:
    struct Partial<T> {
        value: NonNull<T>,
        slot: NonNull<()>,
    }
}

mod detail {
    use std::{
        mem::{size_of, transmute, MaybeUninit},
        num::NonZeroUsize,
        ptr::NonNull,
        sync::atomic::{AtomicPtr, AtomicU32},
    };

    use static_assertions::assert_eq_align;

    pub(crate) mod pool {
        use parking_lot::lock_api::RawMutex;

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
            fn clean(&self, _: &mut T) {}
        }

        // ==== Builder Component: Page Lock ====
        impl super::PageLock for () {
            type LockGuard<'a> = ();
            fn lock(&self) -> Self::LockGuard<'_> {}
        }

        impl super::PageLock for parking_lot::Mutex<()> {
            type LockGuard<'a> = parking_lot::MutexGuard<'a, ()>;

            fn lock(&self) -> Self::LockGuard<'_> {
                self.lock()
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
        free_head: AtomicPtr<Slot<T>>,

        /// If only the strong reference was released (in sync) (i.e. any weak reference presents),
        /// the node will be stored here. Only `sync` checkouts are allowed to access this storage,
        /// as the generation based hot reuse is exclusively permitted for atomic versions.
        free_head_may_weak: AtomicPtr<Slot<T>>,

        fallback_page_size: NonZeroUsize,

        init_func: CreateFn,
        prepare_func: PrepareFn,
        clean_func: CleanFn,

        alloc_lock: AllocLock,

        item_counter: Counter,
    }

    trait ApplyFunc<T>: 'static + Send + Sync {
        fn clean(&self, _: &mut T);
    }

    trait PageLock: 'static + Send + Sync {
        type LockGuard<'a>
        where
            Self: 'a;

        fn lock(&self) -> Self::LockGuard<'_>;
    }

    trait Counter: 'static + Send + Sync {
        fn inc_total_by(&self, total: usize);
        fn inc_free_item_by(&self, free: usize);
        fn dec_free_item_by(&self, free: usize);

        fn total(&self) -> Option<usize>;
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
            todo!()
        }

        fn checkout_local(&self) -> NonNull<Slot<T>> {
            todo!()
        }

        fn allocate_page(&self, page_size: Option<NonZeroUsize>) {
            let _lc = self.alloc_lock.lock();

            let elem_count = page_size.unwrap_or(self.fallback_page_size).get();
            let slot_size = size_of::<Slot<T>>();

            // Offset page payload to write page header contents in it.
            let payload_offset = (size_of::<PageHeader<T>>() + slot_size - 1) / slot_size;
            let alloc_count = payload_offset + elem_count;

            // Alignment of `Slot` must be larger than `PageHeader`. This is ALWAYS true as long as
            // following assertion is satisfied; as `PageHeader` never aligned to other than pointer
            // size.
            assert_eq_align!(PageHeader<()>, Slot<()>);
            assert_eq_align!(PageHeader<u8>, Slot<u8>);
            assert_eq_align!(PageHeader<u16>, Slot<u16>);
            assert_eq_align!(PageHeader<u32>, Slot<u32>);
            assert_eq_align!(PageHeader<*const ()>, Slot<*const ()>);

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
                    value: (self.init_func)(),

                    // SAFETY:
                    // - We're going to initialize next element.
                    // - For last element which points to invalid memory space, will be handled
                    //   after breaking out of this loop.
                    next_free: AtomicPtr::new(unsafe { transmute(slot_ptr.add(1)) }),

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
            let last_elem = unsafe {
                payload_slice
                    .last_mut()
                    .unwrap_unchecked()
                    .assume_init_mut()
            };

            todo!()
        }

        fn total_item(&self) -> Option<usize> {
            todo!()
        }

        fn free_item(&self) -> Option<usize> {
            todo!()
        }

        fn checkin(&self, ptr: NonNull<Slot<T>>) {
            todo!()
        }

        fn checkin_local(&self, ptr: NonNull<Slot<T>>) {
            todo!()
        }
    }

    impl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
        PoolInnerImpl<T, CreateFn, PrepareFn, CleanFn, Cnt, AllocLock>
    where
        T: 'static,
        CreateFn: ApplyFunc<T>,
        PrepareFn: ApplyFunc<T>,
        CleanFn: ApplyFunc<T>,
        Cnt: Counter,
        AllocLock: PageLock,
    {
        fn return_to_head(&self, ptr: NonNull<Slot<T>>) {
            todo!()
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
        next_free: AtomicPtr<Slot<T>>,

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
        // ==== Local API ====

        pub fn release_local(this: NonNull<Self>) {
            todo!()
        }

        pub fn add_ref_local(this: NonNull<Self>) {
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
}

// ========================================================== Unsafe Ref Cell ===|

pub mod unsafe_ref_cell {
    use std::{
        cell::UnsafeCell,
        sync::atomic::{AtomicUsize, Ordering::SeqCst},
    };

    /// Works like using try_lock.unwrap() for every instance, but removing overhead on release
    /// build.
    #[derive(Debug)]
    #[repr(C)] // Let `inner` always laid upon base of this struct
    pub struct UnsafeRefCell<T> {
        inner: UnsafeCell<T>,

        #[cfg(any(debug_assertions, feature = "force-safe-api"))]
        borrow_count: AtomicUsize,

        #[cfg(any(debug_assertions, feature = "force-safe-api"))]
        borrow_mut_count: AtomicUsize,
    }

    #[repr(transparent)]
    pub struct UnsafeRef<'a, T> {
        inner: &'a UnsafeRefCell<T>,
    }

    #[repr(transparent)]
    pub struct UnsafeRefMut<'a, T> {
        inner: &'a mut UnsafeRefCell<T>,
    }

    impl<T> UnsafeRefCell<T> {
        pub fn new(inner: T) -> Self {
            Self {
                inner: UnsafeCell::new(inner),
                borrow_count: AtomicUsize::new(0),
                borrow_mut_count: AtomicUsize::new(0),
            }
        }

        /// Primarily used to compare data address between two cell.
        pub fn as_ptr(&self) -> *const T {
            self.inner.get()
        }

        /// To compare
        pub fn ptr_eq<U>(&self, other: *const U) -> bool {
            self.as_ptr() as usize == other as usize
        }

        pub fn borrow(&self) -> UnsafeRef<'_, T> {
            #[cfg(any(debug_assertions, feature = "force-safe-api"))]
            {
                self.borrow_count.fetch_add(1, SeqCst);

                assert!(
                    self.borrow_mut_count.load(SeqCst) == 0,
                    "Cannot borrow while mutably borrowed"
                )
            }

            UnsafeRef { inner: self }
        }

        pub fn borrow_mut(&mut self) -> UnsafeRefMut<'_, T> {
            #[cfg(any(debug_assertions, feature = "force-safe-api"))]
            {
                assert!(
                    self.borrow_mut_count.fetch_add(1, SeqCst) == 0,
                    "Cannot mutably borrow multiple times"
                );

                assert!(
                    self.borrow_count.load(SeqCst) == 0,
                    "Cannot mutably borrow while borrowed"
                )
            }

            UnsafeRefMut { inner: self }
        }
    }

    #[cfg(any(debug_assertions, feature = "force-safe-api"))]
    impl<T> Drop for UnsafeRefCell<T> {
        fn drop(&mut self) {
            assert!(
                self.borrow_count.load(SeqCst) == 0,
                "Cannot drop while borrowed"
            );
            assert!(
                self.borrow_mut_count.load(SeqCst) == 0,
                "Cannot drop while mutably borrowed"
            );
        }
    }

    impl<'a, T> std::ops::Deref for UnsafeRef<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: At least during debug build or `force-safe-api` is active ...
            unsafe { &*self.inner.inner.get() }
        }
    }

    impl<'a, T> std::ops::Deref for UnsafeRefMut<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: At least during debug build or `force-safe-api` is active ...
            unsafe { &*self.inner.inner.get() }
        }
    }

    impl<'a, T> std::ops::DerefMut for UnsafeRefMut<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: At least during debug build or `force-safe-api` is active ...
            unsafe { &mut *self.inner.inner.get() }
        }
    }

    #[cfg(any(debug_assertions, feature = "force-safe-api"))]
    impl<'a, T> Drop for UnsafeRef<'a, T> {
        fn drop(&mut self) {
            self.inner.borrow_count.fetch_sub(1, SeqCst);
        }
    }

    #[cfg(any(debug_assertions, feature = "force-safe-api"))]
    impl<'a, T> Drop for UnsafeRefMut<'a, T> {
        fn drop(&mut self) {
            self.inner.borrow_mut_count.fetch_sub(1, SeqCst);
        }
    }
}

pub use api::*;
