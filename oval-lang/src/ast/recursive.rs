use crate::recurse;
use crate::spanned::{Span, Spanned};
use alloc::boxed::Box;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::mem::ManuallyDrop;
use crate::alloc_helper::slice;

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Recursive<T: ?Sized>(ManuallyDrop<Box<T>>);

impl<T> Recursive<T> {
    #[inline]
    pub fn new(val: T) -> Self {
        Self::from_box(Box::new(val))
    }
}

impl<T: ?Sized> Recursive<T> {
    pub const fn from_box(boxed: Box<T>) -> Self {
        Self(ManuallyDrop::new(boxed))
    }

    pub fn into_box(self) -> Box<T> {
        let mut this = ManuallyDrop::new(self);
        // Safety: this won't be dropped
        // and this is the only place take is called from
        unsafe { ManuallyDrop::take(&mut this.0) }
    }

    pub fn get_ref(&self) -> &T {
        &self.0
    }

    pub fn with_inner<'a, U: 'a>(&'a self, fun: impl FnOnce(&'a T) -> U) -> U {
        let inner = self.get_ref();
        recurse(move || fun(inner))
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.0
    }

    pub fn with_inner_mut<'a, U: 'a>(&'a mut self, fun: impl FnOnce(&'a mut T) -> U) -> U {
        let inner = self.get_mut();
        recurse(move || fun(inner))
    }
}

impl<T> Recursive<[T]> {
    pub const fn empty_slice() -> Self {
        const { Self::from_box(slice![]) }
    }
}

impl<T: Hash + ?Sized> Hash for Recursive<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.with_inner(|inner| T::hash(inner, state))
    }
}

macro_rules! cmp_trait {
    ($(impl $trait: path {
        $(fn $name: ident -> $ret:ty;)*
    })+) => {
        $(impl<T: ?Sized + $trait> $trait for Recursive<T> {
            $(fn $name(&self, other: &Self) -> $ret {
                let (this, other) = (self.get_ref(), other.get_ref());
                recurse(move || <T as $trait>::$name(this, other))
            })*
        })+
    };
}

cmp_trait! {
    impl PartialEq {
        fn eq -> bool;
    }

    impl Eq {}

    impl PartialOrd {
        fn partial_cmp -> Option<Ordering>;

        fn lt -> bool;
        fn le -> bool;
        fn gt -> bool;
        fn ge -> bool;
    }

    impl Ord {
        fn cmp -> Ordering;
    }
}

impl<T: ?Sized + Spanned> Spanned for Recursive<T> {
    fn span(&self) -> Span {
        self.with_inner(<T as Spanned>::span)
    }
}

impl<T: ?Sized> Drop for Recursive<T> {
    fn drop(&mut self) {
        match core::mem::needs_drop::<T>() {
            true => {
                struct DropGuard<'a, T: ?Sized>(Option<&'a mut Recursive<T>>);

                impl<T: ?Sized> Drop for DropGuard<'_, T> {
                    fn drop(&mut self) {
                        // this handles the case where the closure is NEVER ran
                        // so if the closure RAN and drop panicked; this is skipped
                        // and that is intended
                        if let Some(alive) = self.0.take() {
                            unsafe { ManuallyDrop::drop(&mut alive.0) }
                        }
                    }
                }

                let mut guard = DropGuard(Some(self));

                recurse(move || {
                    unsafe {
                        // Safety: closure can only ever run once;
                        // so this must have a ref right now
                        // since the guard has not been dropped

                        let to_drop = guard.0.take().unwrap_unchecked();
                        // run the probably recursive drop of T as well
                        ManuallyDrop::drop(&mut to_drop.0)
                    }
                })
            }

            // Safety:
            // we are obviously running in a drop impl so we won't be accessed again
            // and this is the fast path since we know T does not need extra stack space
            // and won't be dropped; this is just dealloc
            false => unsafe { ManuallyDrop::drop(&mut self.0) },
        }
    }
}
