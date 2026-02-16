use cfg_if::cfg_if;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

// all mutex implementations must be at least eventually fair (or fully fair)
cfg_if! {
    if #[cfg(feature = "parking_lot")] {
        // parking_lot's mutex is documented to be eventually fair
        type MutexInner<T> = parking_lot::Mutex<T>;
        type MutexGuardInner<'a, T> = parking_lot::MutexGuard<'a, T>;
    } else if #[cfg(feature = "std")] {
        // std mutex has no documentation about fairness
        // make a fair mutex manually
        mod mutex_impl {
            extern crate std;

            use std::{
                cell::UnsafeCell,
                collections::VecDeque,
                ops::{Deref, DerefMut},
                sync::{
                    atomic::{AtomicBool, Ordering},
                    Mutex,
                    PoisonError
                },
                thread::{self, Thread},
            };

            use crate::abort::AbortGuard;

            pub struct FairMutex<T> {
                state: Mutex<State>,
                data: UnsafeCell<T>,
            }

            struct State {
                locked: bool,
                waiters: VecDeque<std::sync::Arc<Waiter>>,
            }

            struct Waiter {
                thread: Thread,
                notified: AtomicBool,
            }

            pub struct FairMutexGuard<'a, T> {
                mutex: &'a FairMutex<T>,
            }

            impl<T> FairMutex<T> {
                pub const fn new(value: T) -> Self {
                    Self {
                        state: Mutex::new(State {
                            locked: false,
                            waiters: VecDeque::new(),
                        }),
                        data: UnsafeCell::new(value),
                    }
                }

                /// Acquire the lock, granting ownership in FIFO order among waiters.
                pub fn lock(&self) -> FairMutexGuard<'_, T> {
                    let mut state = self.state.lock()
                        .unwrap_or_else(PoisonError::into_inner);

                    // fast path; 0 contention
                    if !state.locked && state.waiters.is_empty() {
                        state.locked = true;
                        return FairMutexGuard { mutex: self };
                    }

                    let waiter = std::sync::Arc::new(Waiter {
                        thread: thread::current(),
                        notified: AtomicBool::new(false),
                    });
                    state.waiters.push_back(waiter.clone());
                    // from this point onwards, the waiter is inserted in the queue
                    // don't allow this thread to panic
                    let abort_guard = AbortGuard::new();
                    drop(state);

                    let mutex_guard = loop {
                        if waiter.notified.load(Ordering::Acquire) {
                            break FairMutexGuard { mutex: self };
                        }
                        thread::park();
                    };

                    abort_guard.disarm();

                    mutex_guard
                }

                pub fn into_inner(self) -> T {
                    self.data.into_inner()
                }

                unsafe fn unlock(&self) {
                    // Pop next waiter (if any) while holding the state mutex.
                    let next = {
                        let mut st = self.state.lock()
                            .unwrap_or_else(PoisonError::into_inner);
                        unsafe { core::hint::assert_unchecked(st.locked) }
                        if let Some(w) = st.waiters.pop_front() {
                            // Keep `locked = true` and hand off directly to the next waiter.
                            // (No gap where another thread could steal the lock.)
                            w.notified.store(true, Ordering::Release);
                            Some((w, AbortGuard::new()))
                        } else {
                            st.locked = false;
                            None
                        }
                    };

                    // Unpark outside holding the mutex
                    if let Some((w, guard)) = next {
                        w.thread.unpark();
                        guard.disarm()
                    }
                }
            }

            impl<'a, T> Deref for FairMutexGuard<'a, T> {
                type Target = T;

                fn deref(&self) -> &Self::Target {
                    // Safety: while a guard exists, this thread exclusively owns the lock.
                    unsafe { &*self.mutex.data.get() }
                }
            }

            impl<'a, T> DerefMut for FairMutexGuard<'a, T> {
                fn deref_mut(&mut self) -> &mut Self::Target {
                    // Safety: while a guard exists, this thread exclusively owns the lock.
                    unsafe { &mut *self.mutex.data.get() }
                }
            }

            impl<'a, T> Drop for FairMutexGuard<'a, T> {
                fn drop(&mut self) {
                    unsafe { self.mutex.unlock() }
                }
            }

            // Safety:
            // The mutex can be shared across threads
            // when T is Send (like std::sync::Mutex).
            unsafe impl<T: Send> Send for FairMutex<T> {}
            unsafe impl<T: Send> Sync for FairMutex<T> {}
        }

        type MutexInner<T> = mutex_impl::FairMutex<T>;
        type MutexGuardInner<'a, T> = mutex_impl::FairMutexGuard<'a, T>;
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

    pub fn into_inner(self) -> T {
        self.0.into_inner()
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
