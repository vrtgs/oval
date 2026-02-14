use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;
use bytemuck::Zeroable;
use core::cmp::Ordering;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::ops::Deref;
use core::ptr::NonNull;

pub fn zeroed_slice<T: Zeroable>(len: usize) -> Box<[T]> {
    // Safety: T is Zeroable
    unsafe { Box::<[T]>::new_zeroed_slice(len).assume_init() }
}

pub const fn empty_slice<T>() -> Box<[T]> {
    const {
        let ptr = NonNull::<T>::dangling();
        let fat = core::ptr::slice_from_raw_parts_mut(
            ptr.as_ptr(),
            0
        );

        // Safety: box has the same layout as a raw pointer
        // this is a const hack since Box::from_raw is not const ready
        // https://doc.rust-lang.org/std/boxed/index.html#memory-layout
        unsafe { core::mem::transmute::<*mut [T], Box<[T]>>(fat) }
    }
}

pub fn splat_slice<T: Copy>(base: T, len: usize) -> Box<[T]> {
    let mut boxed = Box::<[T]>::new_uninit_slice(len);
    for loc in boxed.iter_mut() {
        loc.write(base);
    }
    unsafe { boxed.assume_init() }
}

macro_rules! slice {
    [] => { (::alloc::boxed::Box::new([]) as ::alloc::boxed::Box<[_]>) };
    // use the alloc::boxed::box_new intrinsic
    [$($item: expr),+ $(,)?] => { vec![$($item),+].into_boxed_slice() };
    [$elem:expr; $n:expr] => { $crate::alloc_helper::splat_slice($elem, $n) };
}

pub(crate) use slice;


pub fn make_slice<T>(mut func: impl FnMut(usize) -> T, len: usize) -> Box<[T]> {
    let mut vec = Vec::with_capacity(len);
    for i in 0..len {
        vec.push(func(i))
    }
    vec.into_boxed_slice()
}


pub struct RcSlice<T>(Option<Rc<[T]>>);

impl<T> RcSlice<T> {
    pub const fn empty() -> Self {
        Self(None)
    }

    pub fn from_rc(rc: Rc<[T]>) -> Self {
        Self(Some(rc).filter(|rc| !rc.is_empty()))
    }
}

impl<T> Deref for RcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        match self.0.as_deref() {
            Some(slice) => {
                unsafe { core::hint::assert_unchecked(!slice.is_empty()) }
                slice
            },
            None => &[]
        }
    }
}

impl<T> FromIterator<T> for RcSlice<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        if let (_lower @ 0, Some(_upper @ 0)) = iter.size_hint() {
            return Self::empty()
        }

        let rc = Rc::<[T]>::from_iter(iter);
        Self::from_rc(rc)
    }
}

impl<T> Clone for RcSlice<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, source: &Self) {
        self.0.clone_from(&source.0)
    }
}

impl<T: Debug> Debug for RcSlice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        <[T] as Debug>::fmt(self, f)
    }
}

impl<T: Hash> Hash for RcSlice<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <[T] as Hash>::hash(self, state)
    }
}

impl<T: PartialEq> PartialEq for RcSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        <[T] as PartialEq>::eq(self, other)
    }
}

impl<T: Eq> Eq for RcSlice<T> {}

impl<T: PartialOrd> PartialOrd for RcSlice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        <[T] as PartialOrd>::partial_cmp(self, other)
    }
}

impl<T: Ord> Ord for RcSlice<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        <[T] as Ord>::cmp(self, other)
    }
}
