#![no_std]
#![deny(clippy::missing_safety_doc)]

extern crate alloc;

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::ops::{Deref, DerefMut};

pub struct MinSizedCowArray<T, const MIN: usize>(Arc<Vec<T>>);

impl<T, const MIN: usize> MinSizedCowArray<T, MIN> {
    pub fn new(head: [T; MIN]) -> Self {
        Self(Arc::new(Vec::from(head)))
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub fn head(&self) -> &[T; MIN] {
        // FIXME: unchecked
        self.0.first_chunk().unwrap()
    }

    pub fn split_head(&self) -> (&[T; MIN], &[T]) {
        // FIXME: unchecked
        self.0.split_first_chunk().unwrap()
    }

    pub fn tail(&self) -> &[T; MIN] {
        // FIXME: unchecked
        self.0.last_chunk().unwrap()
    }

    pub fn split_tail(&self) -> (&[T], &[T; MIN]) {
        // FIXME: unchecked
        self.0.split_last_chunk().unwrap()
    }

    pub fn from_vec(vec: Vec<T>) -> Result<Self, Vec<T>> {
        if vec.len() < MIN {
            return Err(vec);
        }

        // Safety: vec contains at least MIN elements
        Ok(unsafe { Self::from_vec_unchecked(vec) })
    }

    pub unsafe fn from_vec_unchecked(vec: Vec<T>) -> Self {
        // FIXME: unchecked
        assert!(vec.len() >= MIN);
        Self(Arc::new(vec))
    }

    pub fn get_mut(&mut self) -> Option<MinSizedCowArrayMut<T, MIN>> {
        Arc::get_mut(&mut self.0).map(MinSizedCowArrayMut)
    }
}

impl<T: Clone, const MIN: usize> MinSizedCowArray<T, MIN> {
    pub fn make_mut(&mut self) -> MinSizedCowArrayMut<T, MIN> {
        MinSizedCowArrayMut(Arc::make_mut(&mut self.0))
    }
}

impl<T: Copy, const MIN: usize> MinSizedCowArray<T, MIN> {
    pub fn copy_from_slice(slice: &[T]) -> Option<Self> {
        if slice.len() < MIN {
            return None;
        }

        // Safety: just made sure that slice contains MIN elements
        Some(unsafe { Self::copy_from_slice_unchecked(slice) })
    }

    /// # Safety
    /// * `slice` is at least `MIN` in length
    pub unsafe fn copy_from_slice_unchecked(slice: &[T]) -> Self {
        // FIXME: unchecked
        Self(Arc::new(<[T]>::into_vec(Box::<[T]>::from(slice))))
    }

    /// Creates a deep copy of this Cow
    pub fn deep_copy(&self) -> Self {
        // Safety: Self is always at least MIN in length
        unsafe { Self::copy_from_slice_unchecked(self) }
    }
}

impl<T: Clone, const MIN: usize> MinSizedCowArray<T, MIN> {
    pub fn clone_from_slice(slice: &[T]) -> Option<Self> {
        if slice.len() < MIN {
            return None;
        }

        // Safety: just made sure that slice contains MIN elements
        Some(unsafe { Self::clone_from_slice_unchecked(slice) })
    }

    pub unsafe fn clone_from_slice_unchecked(slice: &[T]) -> Self {
        // FIXME: unchecked
        assert!(slice.len() >= MIN);
        Self(Arc::new(slice.to_vec()))
    }

    pub fn deep_clone(&self) -> Self {
        // Safety:
        // Self is always at least MIN in length
        // and layout is valid for self
        unsafe { Self::clone_from_slice_unchecked(self) }
    }
}

impl<T, const MIN: usize> Deref for MinSizedCowArray<T, MIN> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        let slice = &**self.0;
        // FIXME: unchecked
        assert!(slice.len() >= MIN);
        slice
    }
}

pub struct MinSizedCowArrayMut<'a, T, const MIN: usize>(&'a mut Vec<T>);

impl<'a, T, const MIN: usize> MinSizedCowArrayMut<'a, T, MIN> {
    pub fn head(&self) -> &[T; MIN] {
        self.0.first_chunk().unwrap()
    }

    pub fn head_mut(&mut self) -> &mut [T; MIN] {
        self.0.first_chunk_mut().unwrap()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    pub fn push(&mut self, item: T) {
        self.0.push(item)
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len() <= MIN {
            // FIXME: unchecked
            assert_eq!(self.len(), MIN);
            return None;
        }

        self.0.pop()
    }
}

impl<T, const MIN: usize> Deref for MinSizedCowArrayMut<'_, T, MIN> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T, const MIN: usize> DerefMut for MinSizedCowArrayMut<'_, T, MIN> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

#[repr(transparent)]
pub struct CowArray<T>(MinSizedCowArray<T, 0>);

impl<T> CowArray<T> {
    pub fn new() -> Self {
        Self(MinSizedCowArray::new([]))
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        // Safety: MIN = 0
        // all lengths are >= 0
        Self(unsafe { MinSizedCowArray::from_vec_unchecked(vec) })
    }

    pub fn get_mut(&mut self) -> Option<CowArrayMut<T>> {
        self.0.get_mut().map(CowArrayMut)
    }
}

impl<T: Copy> CowArray<T> {
    pub fn copy_from_slice(slice: &[T]) -> Self {
        // Safety: see comment in Self::from_vec
        Self(unsafe { MinSizedCowArray::copy_from_slice_unchecked(slice) })
    }
}

impl<T: Clone> CowArray<T> {
    pub fn clone_from_slice(slice: &[T]) -> Self {
        // Safety: see comment in Self::from_vec
        Self(unsafe { MinSizedCowArray::clone_from_slice_unchecked(slice) })
    }
}

impl<T> Deref for CowArray<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[repr(transparent)]
pub struct CowArrayMut<'a, T>(MinSizedCowArrayMut<'a, T, 0>);

impl<T> CowArrayMut<'_, T> {
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    pub fn push(&mut self, item: T) {
        self.0.push(item)
    }

    pub fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

impl<'a, T> Deref for CowArrayMut<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T> DerefMut for CowArrayMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> FromIterator<T> for CowArray<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        CowArray::from_vec(Vec::from_iter(iter))
    }
}

macro_rules! same_impl {
    (
        $(impl<$T: ident $(: $bound: path)?> ($trait: path) for $(&$life: lifetime)?Cows {
            $($tt:item)*
        })+
    ) => {
        $(impl<$($life,)? $T $(: $bound)?, const MIN: usize> $trait for $(& $life)?MinSizedCowArray<$T, MIN> {
            $($tt)*
        }
        impl<$($life,)? $T $(: $bound)?> $trait for $(& $life)? CowArray<$T> {
            $($tt)*
        })+
    };
}

same_impl! {
    impl<T> (Clone) for Cows {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }

        fn clone_from(&mut self, source: &Self) {
            self.0.clone_from(&source.0)
        }
    }

    impl<T: Debug> (Debug) for Cows {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            <[T] as Debug>::fmt(self, f)
        }
    }


    impl<T: Hash> (Hash) for Cows {
        fn hash<H: Hasher>(&self, state: &mut H) {
            <[T] as Hash>::hash(self, state)
        }
    }


    impl<T: PartialEq> (PartialEq) for Cows {
        fn eq(&self, other: &Self) -> bool {
            <[T] as PartialEq>::eq(self, other)
        }
    }

    impl<T: Eq> (Eq) for Cows {}

    impl<T: PartialOrd> (PartialOrd) for Cows {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            <[T] as PartialOrd>::partial_cmp(self, other)
        }
    }

    impl<T: Ord> (Ord) for Cows {
        fn cmp(&self, other: &Self) -> Ordering {
            <[T] as Ord>::cmp(self, other)
        }
    }

    impl<T> (IntoIterator) for &'a Cows {
        type Item = &'a T;
        type IntoIter = core::slice::Iter<'a, T>;

        fn into_iter(self) -> Self::IntoIter {
            (**self).iter()
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use alloc::string::String;
    use alloc::vec;

    use super::*;

    #[test]
    fn test_min_sized_new() {
        let arr = MinSizedCowArray::new([1, 2, 3]);
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.capacity(), 3);
        assert_eq!(&*arr, &[1, 2, 3]);
    }

    #[test]
    fn test_min_sized_from_vec() {
        let vec = vec![1, 2, 3, 4];
        let arr = MinSizedCowArray::<i32, 3>::from_vec(vec.clone()).unwrap();
        assert_eq!(&*arr, &vec[..]);
        assert!(arr.capacity() >= arr.len());

        let short_vec = vec![1];
        assert!(MinSizedCowArray::<_, 2>::from_vec(short_vec).is_err());
    }

    #[test]
    fn test_min_sized_copy_from_slice() {
        let slice = &[1, 2, 3, 4];
        let arr = MinSizedCowArray::<_, 2>::copy_from_slice(slice).unwrap();
        assert_eq!(arr.len(), 4);
        assert_eq!(&*arr, slice);

        assert!(MinSizedCowArray::<_, 5>::copy_from_slice(slice).is_none());
    }

    #[test]
    fn test_min_sized_clone_from_slice() {
        let slice = &[String::from("a"), String::from("b")];
        let arr = MinSizedCowArray::<_, 2>::clone_from_slice(slice).unwrap();
        assert_eq!(arr.len(), 2);
        assert_eq!(&*arr, slice);

        assert!(MinSizedCowArray::<_, 3>::clone_from_slice(slice).is_none());
    }

    #[test]
    fn test_min_sized_clone() {
        let arr = MinSizedCowArray::new([1, 2, 3]);
        let arr2 = arr.clone();
        assert_eq!(arr.len(), arr2.len());
        assert_eq!(&*arr, &*arr2);
    }

    #[test]
    fn test_min_sized_deref() {
        let arr = MinSizedCowArray::new([1, 2, 3]);
        let slice: &[i32] = &arr;
        assert_eq!(*slice, [1, 2, 3]);
    }

    #[test]
    fn test_min_sized_ptr_accessors() {
        let arr = MinSizedCowArray::new([1, 2, 3]);
        let ptr = arr.as_ptr();

        unsafe {
            assert_eq!(*ptr, 1);
        }
    }

    #[test]
    fn test_cow_array_new() {
        let arr = CowArray::<i32>::new();
        assert_eq!(arr.len(), 0);
        assert_eq!(arr.capacity(), 0);
    }

    #[test]
    fn test_cow_array_from_vec() {
        let vec = vec![1, 2, 3];
        let arr = CowArray::from_vec(vec.clone());
        assert_eq!(arr.len(), 3);
        assert_eq!(&*arr.0, &vec[..]);
    }

    #[test]
    fn test_cow_array_copy_from_slice() {
        let slice = &[1, 2, 3];
        let arr = CowArray::copy_from_slice(slice);
        assert_eq!(arr.len(), 3);
        assert_eq!(&*arr.0, slice);
    }

    #[test]
    fn test_cow_array_clone_from_slice() {
        let slice = &[String::from("a"), String::from("b")];
        let arr = CowArray::clone_from_slice(slice);
        assert_eq!(arr.len(), 2);
        assert_eq!(&*arr.0, slice);
    }

    #[test]
    fn test_cow_array_clone() {
        let arr = CowArray::copy_from_slice(&[1, 2, 3]);
        let arr2 = arr.clone();
        assert_eq!(&*arr.0, &*arr2.0);
    }

    #[test]
    fn test_cow_array_ptr_accessors() {
        let slice = &[1, 2, 3];
        let arr = CowArray::copy_from_slice(slice);
        let ptr = arr.as_ptr();

        unsafe {
            for (i, element) in slice.iter().enumerate() {
                assert_eq!(*ptr.add(i), *element);
            }
        }
    }

    #[test]
    fn test_drop_semantics() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;

        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let arr = MinSizedCowArray::new([DropCounter, DropCounter]);
            let _arr2 = arr.clone();
            let _arr3 = arr.clone();
        }

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn test_make_unique_on_write() {
        let mut arr = MinSizedCowArray::new([1, 2, 3]);
        let arr2 = arr.clone();

        // Shouldn't be able to get mutable reference while shared
        assert!(MinSizedCowArray::get_mut(&mut arr).is_none());

        drop(arr2);

        // Now should be able to get mutable reference
        assert!(MinSizedCowArray::get_mut(&mut arr).is_some());
    }

    #[test]
    fn test_large_allocation() {
        let mut vec = vec![0; 1024];
        for (i, loc) in vec.iter_mut().enumerate() {
            *loc = i
        }
        let arr = MinSizedCowArray::<_, 512>::from_vec(vec.clone()).unwrap();
        assert_eq!(arr.len(), 1024);
        assert!(arr.capacity() >= 1024);
        assert_eq!(&*arr, &vec[..]);
    }
}
