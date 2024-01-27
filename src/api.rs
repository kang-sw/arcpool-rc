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
    /// Number of allocations cannot exceed (2^32 - 3)
    pub fn allocate_page(&self, page_size: impl TryInto<NonZeroUsize>) {
        self.inner.allocate_page(page_size.try_into().ok());
    }

    pub fn downgrade(&self) -> WeakPool<T> {
        WeakPool {
            inner: Arc::downgrade(&self.inner),
        }
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
}

// ========================================================== *Partial* API ===|

// TODO:
struct Partial<T> {
    value: NonNull<T>,
    slot: NonNull<()>,
}
