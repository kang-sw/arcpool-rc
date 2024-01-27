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
