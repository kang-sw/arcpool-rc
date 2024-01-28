use std::{
    num::NonZeroUsize,
    ptr::NonNull,
    sync::{Arc, Weak},
};

use crate::detail::{PoolInner, Slot};

#[derive(Clone)]
pub struct Pool<T> {
    pub(super) inner: Arc<dyn PoolInner<T>>,
}

#[derive(Clone)]
pub struct WeakPool<T> {
    inner: Weak<dyn PoolInner<T>>,
}

impl<T> Pool<T>
where
    T: 'static,
{
    /// Allocate new item from pool. If no free slot presents, new page will be allocated.
    ///
    /// The returned item will automatically be checked in when dropped. The returned item is not
    /// guaranteed to be unique reference which can be accessed through [`PoolItem::get_mut`].
    pub fn checkout(&self) -> PoolItem<T>
    where
        T: Send + Sync,
    {
        PoolItem {
            slot: self.inner.checkout_sync(),
        }
    }

    /// Allocate a new item from the pool as a local object. This object can contain non-send,
    /// non-sync elements, and utilizes optimized intrinsics for cloning handles. (i.e., it
    /// functions like [`std::rc::Rc`] instead of [`std::sync::Arc`]).
    ///
    /// Although it returns a non-send, non-sync handle for the checked-out value, the inner value
    /// must be marked as [`Send`]. This is because, after checkout, the object will not be dropped
    /// but recycled, and it may be checked out again from a different thread.
    ///
    /// The returned item is guaranteed to be unique reference, that initial call to
    /// [`LocalPoolItem::get_mut`] always succeed.
    pub fn checkout_local(&self) -> LocalPoolItem<T>
    where
        T: Send,
    {
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

    /// Downgrade to weak pool reference.
    pub fn downgrade(&self) -> WeakPool<T> {
        WeakPool {
            inner: Arc::downgrade(&self.inner),
        }
    }

    /// Get number of totally created elements. Returns `None` if the counter feature wasn't
    /// enabled for this pool.
    pub fn total_item_len(&self) -> Option<usize> {
        self.inner.num_total_items()
    }

    /// Get number of unused items inside the pool.
    pub fn free_item_len(&self) -> Option<usize> {
        self.inner.num_free_items()
    }
}

/// Upgrade to weak pool reference.
impl<T> WeakPool<T>
where
    T: 'static,
{
    pub fn upgrade(&self) -> Option<Pool<T>> {
        self.inner.upgrade().map(|inner| Pool { inner })
    }
}

// ========================================================== Local Pool API ===|

// TODO: A totally unique reference to Pool<T> can be downgraded to LocalPool
//   - Which disables any atomic variable checking

// ========================================================== Pool Item ===|

pub struct PoolItem<T: 'static> {
    slot: NonNull<Slot<T>>,
}

pub struct WeakPoolItem<T: 'static> {
    slot: Option<NonNull<Slot<T>>>,
    gen: u32,
}

unsafe impl<T: Send + Sync> Send for PoolItem<T> {}
unsafe impl<T: Send + Sync> Sync for PoolItem<T> {}
unsafe impl<T: Send + Sync> Send for WeakPoolItem<T> {}
unsafe impl<T: Send + Sync> Sync for WeakPoolItem<T> {}

// ==== Impls ====

/// Provide default implementation as `expired` default pointer.
impl<T: 'static> Default for WeakPoolItem<T> {
    fn default() -> Self {
        Self {
            slot: None,
            gen: u32::MAX,
        }
    }
}

impl<T: 'static + Send + Sync> PoolItem<T> {
    /// Tries to retrieve mutable reference of pulled object. It returns valid object only when this
    /// handle is solely unique reference (including weak) for inner value.
    pub fn get_mut(&self) -> Option<&mut T> {
        Slot::try_mut(self.slot)
    }

    pub fn downgrade(&self) -> WeakPoolItem<T> {
        WeakPoolItem {
            gen: Slot::downgrade(self.slot),
            slot: Some(self.slot),
        }
    }

    pub fn owner(&self) -> Pool<T> {
        Pool {
            inner: Slot::get_owner_arc(self.slot),
        }
    }
}

impl<T: 'static + Send + Sync> WeakPoolItem<T> {
    pub fn upgrade(&self) -> Option<PoolItem<T>> {
        Slot::try_upgrade(self.slot?, self.gen).map(|slot| PoolItem { slot })
    }
}

impl<T: 'static + Send + Sync> Clone for PoolItem<T> {
    fn clone(&self) -> Self {
        // Since we're already holding a strong reference, it's okay to add reference at any moment.
        Slot::add_ref(self.slot);

        Self { slot: self.slot }
    }
}

impl<T: 'static + Send + Sync> Clone for WeakPoolItem<T> {
    fn clone(&self) -> Self {
        Self {
            gen: self.gen,

            // We conditionally clone only if it's not expired. This is not to create expired
            // reference repeatedly, which simply delays release of reusable memory space.
            slot: self
                .slot
                .and_then(|slot| Slot::try_clone_weak(slot, self.gen)),
        }
    }
}

impl<T> Drop for PoolItem<T> {
    fn drop(&mut self) {
        Slot::release(self.slot)
    }
}

impl<T> std::ops::Deref for PoolItem<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // The value is laid directly upon the slot.
        unsafe { &*(self.slot.as_ptr() as *const T) }
    }
}

impl<T> Drop for WeakPoolItem<T> {
    fn drop(&mut self) {
        if let Some(slot) = self.slot {
            Slot::weak_release(slot)
        }
    }
}

// ========================================================== Local Pool Item ===|

/// Pool item for non-sync items.
///
/// This handle works same way with [`std::rc::Rc`].
pub struct LocalPoolItem<T> {
    slot: NonNull<Slot<T>>,
}

/// Pool item for non-sync items.
pub struct WeakLocalPoolItem<T> {
    slot: Option<NonNull<Slot<T>>>,
}

// ========================================================== *Partial* API ===|

// TODO:
struct Partial<T> {
    value: NonNull<T>,
    slot: NonNull<()>,
}
