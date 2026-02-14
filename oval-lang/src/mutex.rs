use cfg_if::cfg_if;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

// all mutex implementations must be at least eventually fair (or fully fair)
cfg_if! {
    if #[cfg(feature = "parking_lot")] {
        // documented to be eventually fair
        type MutexInner<T> = parking_lot::Mutex<T>;
        type MutexGuardInner<'a, T> = parking_lot::MutexGuard<'a, T>;
    } else if #[cfg(feature = "std")] {
        // std mutex has no documentation about fairness
        // make a fair mutex manually
        mod mutex_impl {}
        compile_error!("std mutex not implemented yet")
    } else if #[cfg(feature = "spin")] {
        // this is only eventually fair; the fully fair mutex (fifo) is the Ticket mutex
        type MutexInner<T> = spin::mutex::FairMutex<T>;
        type MutexGuardInner<'a, T> = spin::mutex::FairMutexGuard<'a, T>;
    } else {
        compile_error!("no mutex provider found, enable either parking_lot, std or spin")
    }
}


/// An eventually fair mutex
pub struct Mutex<T>(MutexInner<T>);

impl<T> Mutex<T> {
    #[inline(always)]
    pub const fn new(data: T) -> Self {
        Self(MutexInner::new(data))
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    /// The exact behavior on locking a mutex in the thread which already holds the lock is left unspecified.
    /// However, this function will not return on the second call (it might panic or deadlock, for example).
    #[inline(always)]
    pub fn lock(&self) -> MutexGuard<'_, T> {
        let guard = self.0.lock();
        MutexGuard {
            guard,
            _phantom: PhantomData
        }
    }
}

#[must_use = "if unused the Mutex will immediately unlock"]
// FIXME #![feature(must_not_suspend)]
// #[must_not_suspend = "holding a MutexGuard across suspend \
//                       points can cause deadlocks, delays, \
//                       and cause Futures to not implement `Send`"]
pub struct MutexGuard<'a, T> {
    guard: MutexGuardInner<'a, T>,
    _phantom: PhantomData<*const ()> // make sure that a mutex guard is never send nor sync
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.guard
    }
}

impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.guard
    }
}
