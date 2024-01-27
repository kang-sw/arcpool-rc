pub mod api {
    use std::{
        ptr::NonNull,
        sync::{Arc, Weak},
    };

    use crate::detail::{Node, PoolInner};

    const DEFAULT_PAGE_SIZE: usize = 32;

    #[derive(Clone)]
    pub struct Pool<T> {
        inner: Arc<PoolInner<T>>,
    }

    #[derive(Clone)]
    pub struct WeakPool<T> {
        inner: Weak<PoolInner<T>>,
    }

    impl<T> Pool<T> {
        /// Allocate new item from pool. If no free slot presents, new page will be allocated.
        pub fn allocate(&self) -> PoolItem<T> {
            todo!()
        }

        /// Try mutate page size. It is guaranteed to succeed right after
        pub fn page_size_mut(&self) -> Option<&mut usize> {
            todo!()
        }

        /// Returns
        pub fn page_size(&self) -> usize {
            todo!()
        }

        /// Forcibly reserve a page with given size. If the size is not specified,
        pub fn reserve_page(&self, page_size: impl TryInto<usize>) {
            todo!()
        }
    }

    // ==== Pool Item ====

    pub struct PoolItem<T> {
        ptr: NonNull<Node<T>>,
    }

    pub struct PoolItemWeak<T> {
        ptr: NonNull<Node<T>>,
    }

    // ==== Partial Item API ====

    pub struct PartialItem<T> {
        raw: NonNull<()>,
        drop: unsafe fn(NonNull<()>),
        val: NonNull<T>,
    }

    pub struct PartialItemWeak<T> {
        raw: NonNull<()>,
        drop: unsafe fn(NonNull<()>),
        val: NonNull<T>,
    }
}

mod detail {
    use std::{
        mem::MaybeUninit,
        ptr::NonNull,
        sync::atomic::{AtomicPtr, AtomicU32, AtomicU64, AtomicUsize},
    };

    trait InitCleanupFn<T> {
        /// Allocate and initiate
        fn init_page(&self, len: usize) -> NonNull<PageHeader<T>>;
        fn cleanup(&self, _: &mut T);

        fn lock_alloc(&self);
        fn unlock_alloc(&self);
    }

    pub(crate) struct PoolInner<T> {
        head_free: AtomicPtr<Node<T>>,
        alloc_mutex: Option<parking_lot::Mutex<()>>,
        init_func: Box<dyn InitCleanupFn<T>>,
    }

    pub(crate) mod builder {
        use std::num::NonZeroUsize;

        pub struct Builder<T, FInit, FClean> {
            _marker_ty: std::marker::PhantomData<T>,
            page_size: Option<NonZeroUsize>,
            init_func: FInit,
            clean_func: FClean,
            use_page_alloc_lock: bool,
        }
    }

    /// Memory allocation is:
    ///
    /// ```text
    ///     |-- PageHeader --|-- Node<T> ---- ... ->
    /// ```
    ///
    ///
    struct PageHeader<T> {
        owner: NonNull<PoolInner<T>>,
        page_length: usize,

        /// Address of the
        array_start: NonNull<Node<T>>,

        /// Only referred during array destruction.
        dealloc_counter: AtomicUsize,
    }

    pub(crate) struct Node<T> {
        value: MaybeUninit<T>,
        next_free: AtomicPtr<Node<T>>,

        /// 63...32: Generation, 31...0:
        slot_0: AtomicU64,
        weak_count: AtomicU32,

        /// An index offset from start of the byte buffers
        index_offset: u32,
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
