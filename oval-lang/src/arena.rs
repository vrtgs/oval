use crate::hashed::HashTable;
use alloc::vec;
use alloc::vec::Vec;
use cfg_if::cfg_if;
use core::borrow::Borrow;
use core::fmt::{Debug, Formatter};
use core::hash::{BuildHasher, Hash};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::num::NonZero;
use core::ops::{Index, IndexMut};
use hashbrown::hash_table::Entry;

cfg_if! {
    // the rust core lib guarantees usize::BITS >= 16
    // and so no need to check 8 bit widths
    // and there is no need to use a 32 bit integer
    // to represent a handle on a 16 bit machine
    if #[cfg(target_pointer_width = "16")] {
        pub(crate) type HandleInt = u16;
    } else {
        pub(crate) type HandleInt = u32;
    }
}

#[inline(always)]
const fn handle_to_usize(symbol_inner: HandleInt) -> usize {
    const { assert!(usize::BITS >= HandleInt::BITS) }

    symbol_inner as usize
}

const fn usize_to_handle(symbol_inner: usize) -> Option<HandleInt> {
    const {
        assert!(HandleInt::MIN == 0 && HandleInt::BITS <= usize::BITS);
    }

    // casting InnerSymbol::MAX as usize is valid
    // this is because usize is always at least as big as InnerSymbol if not bigger
    if symbol_inner > HandleInt::MAX as usize {
        return None
    }

    Some(symbol_inner as HandleInt)
}


#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub(crate) struct HandleRaw(NonZero<HandleInt>);

impl HandleRaw {
    pub(crate) const MAX: Self = Self(NonZero::<HandleInt>::MAX);

    #[inline(always)]
    pub(crate) const fn usize_to_handle_int(handle: usize) -> Option<HandleInt> {
        usize_to_handle(handle)
    }

    #[inline(always)]
    pub(crate) const fn handle_count_to_usize(handle: HandleInt) -> usize {
        handle_to_usize(handle)
    }


    #[inline(always)]
    pub(crate) const fn from_handle_int(handle: HandleInt) -> Option<Self> {
        let Some(inner) = handle.checked_add(1) else {
            return None;
        };
        // Safety: if x + 1 exists and x is <= 0 then x + 1 is by definition > 0
        let inner = unsafe { NonZero::new_unchecked(inner) };
        Some(Self(inner))
    }

    #[inline]
    pub(crate) const fn new(handle: usize) -> Option<Self> {
        let Some(x) = usize_to_handle(handle) else {
            return None;
        };

        Self::from_handle_int(x)
    }

    #[inline(always)]
    pub(crate) const fn as_handle_int(self) -> HandleInt {
        // Safety: self.0 is > 0 since InnerHandle is unsigned
        //         and since its NonZero this holds true
        unsafe { self.0.get().unchecked_sub(1) }
    }

    #[inline(always)]
    pub(crate) const fn get(self) -> usize {
        handle_to_usize(self.as_handle_int())
    }
}

/// # Safety
/// the type implementing this must have the same layout as HandleRaw;
/// as in
/// ```no_compile
/// #[repr(transparent)]
/// struct Foo(HandleRaw);
/// ```
/// and MUST be valid to bitcast to and from a HandleRaw and MUST not overide any methods
/// and all comparison methods must be equal to the result of `to_raw(a) cmp to_raw(b)`
pub(crate) unsafe trait Handle: Ord + Sized + Copy + Send + Sync + 'static {
    fn get(self) -> usize {
        to_raw_handle(self).get()
    }
}

unsafe impl Handle for HandleRaw {}


#[inline(always)]
pub(crate) const unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
    // this version of transmute allows post monomorphization checks for size
    // since normal `transmute` checks sizes pre monomorphization
    const { assert!(size_of::<Src>() == size_of::<Dst>()); }

    #[repr(C)]
    union Transmute<Src, Dst> {
        src: ManuallyDrop<Src>,
        dst: ManuallyDrop<Dst>
    }

    let onion = Transmute { src: ManuallyDrop::new(src) };

    ManuallyDrop::into_inner(unsafe { onion.dst })
}

#[inline(always)]
pub(crate) const fn to_raw_handle<H: Handle>(handle: H) -> HandleRaw {
    // Safety:
    // the `Handle` states all implementors must have the same layout as HandleRaw
    unsafe { transmute::<H, HandleRaw>(handle) }
}

#[inline(always)]
pub(crate) const fn from_raw_handle<H: Handle>(handle: HandleRaw) -> H {
    // Safety:
    // the `Handle` states all implementors must have the same layout as HandleRaw
    unsafe { transmute::<HandleRaw, H>(handle) }
}


pub(crate) trait Storable {
    type Handle: Handle;
}

/// # Safety
/// must always satisfy the following
/// (the following program should NOT panic for a given storable
/// ```no_compile
/// let vec = Self::initial_vec();
/// if !vec.is_empty() {
///     let max_index = vec.len() - 1;
///     let _handle = HandleRaw::new(max_index).unwrap();
/// }
/// ```
pub(crate) unsafe trait Constructable: Storable {
    fn initial_vec() -> Vec<Self> where Self: Sized;
}

pub(crate) trait EmptyConstructable: Storable {}

unsafe impl<E: ?Sized + EmptyConstructable> Constructable for E {
    fn initial_vec() -> Vec<Self>
    where
        Self: Sized,
    {
        vec![]
    }
}

pub(crate) unsafe trait InternableStore {
    type StoredAs: Borrow<Self>;

    fn initial_vec() -> Vec<Self::StoredAs>;
}

/// # Safety
/// initial state must contain elements equal to initial_vec in length
///
/// each element should hash the same and be equal to that of the initial_vec
/// but this isnt a hard requirement for safety; unlike length
pub(crate) unsafe trait Internable: InternableStore + Constructable + Hash + Eq + 'static {}

pub(crate) trait InternableSimple: Sized + Constructable + Hash + Eq + 'static {}

unsafe impl<I: InternableSimple> InternableStore for I {
    type StoredAs = I;

    fn initial_vec() -> Vec<Self::StoredAs> {
        <I as Constructable>::initial_vec()
    }
}

unsafe impl<I: ?Sized + InternableStore + Constructable + Hash + Eq + 'static> Internable for I {}


pub(crate) struct Arena<T>(Vec<T>);

impl<T: Storable + Debug> Debug for Arena<T>
    where T::Handle: Debug
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f
            .debug_map()
            .entries(self.0.iter().enumerate().map(|(i, val)| {
                (from_raw_handle::<T::Handle>(HandleRaw::new(i).unwrap()), val)
            }))
            .finish()
    }
}

pub(crate) struct ArenaSlot<'a, T>(&'a mut Arena<T>);

impl<'a, T> ArenaSlot<'a, T> {
    pub fn insert(self, item: T) -> &'a mut T {
        let vec = &mut self.0.0;

        // SAFETY:
        // invariant; the vector in self.0.0
        // has len() + 1 >= capacity
        // therfore len() + 1 exists
        // and there is at least room for one more element
        unsafe {
            let old_len = vec.len();
            let new_len = old_len.unchecked_add(1);
            let slot = vec.spare_capacity_mut().first_mut().unwrap_unchecked();
            slot.write(item);
            vec.set_len(new_len);
            vec.get_unchecked_mut(old_len)
        }
    }
}

impl<T: Constructable> Arena<T> {
    pub fn new() -> Self {
        Self(T::initial_vec())
    }
}

impl<T: EmptyConstructable> Arena<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }
}

impl<T: Storable> Arena<T> {
    #[must_use]
    pub fn try_reserve(&mut self) -> Option<(T::Handle, ArenaSlot<'_, T>)> {
        let handle = HandleRaw::new(self.0.len())?;
        // Safety after this call self.0 vector
        // has capacity >= len() + 1
        self.0.try_reserve(1).ok()?;
        let slot = ArenaSlot(self);
        Some((from_raw_handle(handle), slot))
    }

    #[must_use]
    pub fn reserve(&mut self) -> (T::Handle, ArenaSlot<'_, T>) {
        self.try_reserve().unwrap()
    }

    #[must_use]
    pub fn try_store(&mut self, item: T) -> Option<T::Handle> {
        let (handle, slot) = self.try_reserve()?;
        slot.insert(item);
        Some(handle)
    }

    #[must_use]
    pub fn store(&mut self, item: T) -> T::Handle {
        self.try_store(item).expect("arena out of space")
    }

    #[must_use]
    pub fn get(&self, handle: T::Handle) -> Option<&T> {
        self.0.get(to_raw_handle(handle).get())
    }

    #[must_use]
    pub unsafe fn get_unchecked(&self, handle: T::Handle) -> &T {
        unsafe { self.0.get_unchecked(to_raw_handle(handle).get()) }
    }

    #[must_use]
    pub fn get_mut(&mut self, handle: T::Handle) -> Option<&mut T> {
        self.0.get_mut(to_raw_handle(handle).get())
    }

    #[must_use]
    pub fn get_disjoint_mut<const N: usize>(&mut self, handles: [T::Handle; N]) -> Option<[&mut T; N]> {
        let handles = handles.map(|handle| {
            to_raw_handle(handle).get()
        });

        self
            .0
            .get_disjoint_mut(handles)
            .ok()
    }

    pub fn len(&self) -> usize {
        let len = self.0.len();
        unsafe {
            // if MAX == usize::MAX then len < usize::MAX holds true;
            // since for all slices len must be < isize::MAX as usize
            // if MAX < usize::MAX then len < MAX + 1 must hold true;
            // since all elements inside this vector must point to valid handles
            core::hint::assert_unchecked(len < const { handle_to_usize(HandleInt::MAX) })
        }
        len
    }

    pub fn count(&self) -> HandleInt {
        // Safety: there are only ever HandleCount elements inside a vector
        unsafe { usize_to_handle(self.len()).unwrap_unchecked() }
    }

    pub fn make_side_table<V>(&self) -> ArenaMap<T::Handle, V> {
        // Safety: all indices of an array of length self.len() have a valid HandleRaw associated
        unsafe { ArenaMap::new_with_length_unchecked(self.len()) }
    }

    pub fn map_cloned<U: Storable<Handle=T::Handle>>(&self, map: impl FnMut(&T) -> U) -> Arena<U> {
        Arena(self.0.iter().map(map).collect())
    }

    pub fn sparse_table_builder<V>(&self) -> SparseArenaMapBuilder<T::Handle, V> {
        SparseArenaMap::builder()
    }

    pub fn map_to<U: Storable<Handle=T::Handle>>(self, map: impl FnMut(T) -> U) -> Arena<U> {
        Arena(self.0.into_iter().map(map).collect())
    }
}

macro_rules! make_iter {
    ($this: expr; iter with $iter: ident) => {{
        let this = $this;
        let _: Arena<_> = *this;
        this.0.$iter().enumerate().map(|(i, item)| {
            let handle = unsafe { HandleRaw::new(i).unwrap_unchecked() };
            let handle = from_raw_handle::<T::Handle>(handle);
            (handle, item)
        })
    }};
}

impl<T: Storable> Arena<T> {
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item=(T::Handle, &'a T)> + 'a + use<'a, T> {
        make_iter!(self; iter with iter)
    }

    pub fn iter_mut<'a>(&'a mut self) -> impl DoubleEndedIterator<Item=(T::Handle, &'a mut T)> + 'a + use<'a, T> {
        make_iter!(self; iter with iter_mut)
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item=T::Handle> + 'static + use<T> {
        (0..self.0.len()).map(|i| {
            from_raw_handle(unsafe { HandleRaw::new(i).unwrap_unchecked() })
        })
    }
}

impl<T: Storable> Index<T::Handle> for Arena<T> {
    type Output = T;

    fn index(&self, index: T::Handle) -> &Self::Output {
        self.get(index).expect("invalid handle")
    }
}

impl<T: Storable> IndexMut<T::Handle> for Arena<T> {
    fn index_mut(&mut self, index: T::Handle) -> &mut Self::Output {
        self.get_mut(index).expect("invalid handle")
    }
}

struct Metadata<K, V> {
    value: Option<V>,
    _phantom: PhantomData<K>
}

impl<K: Handle, V> Storable for Metadata<K, V> {
    type Handle = K;
}

pub struct ArenaMap<K, V>(Arena<Metadata<K, V>>);
pub struct FilledArenaMap<K, V>(ArenaMap<K, V>);

impl<K: Handle, V> ArenaMap<K, V> {
    fn is_valid_length(len: usize) -> bool {
        len == 0 || HandleRaw::new(len - 1).is_some()
    }

    /// # Safety
    /// all indices of an array of length self.len() must have a valid HandleRaw associated
    pub unsafe fn new_with_length_unchecked(len: usize) -> Self {
        unsafe { core::hint::assert_unchecked(Self::is_valid_length(len)) }
        let mut vec = Vec::new();
        vec.resize_with(len, || Metadata { value: None, _phantom: PhantomData });
        ArenaMap(Arena(vec))
    }

    pub fn new_with_length(len: usize) -> Self {
        assert!(Self::is_valid_length(len));
        unsafe { Self::new_with_length_unchecked(len) }
    }
    
    pub unsafe fn get_unchecked(&self, key: K) -> &V {
        unsafe {
            self.0.get_unchecked(key).value.as_ref().unwrap_unchecked()
        }
    }

    pub fn get(&self, key: K) -> Option<&V> {
        self.0[key].value.as_ref()
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.0[key].value.as_mut()
    }

    pub fn insert(&mut self, key: K, value: V) -> &mut V {
        self.0[key].value.insert(value)
    }

    pub fn remove(&mut self, key: K) -> Option<V> {
        self.0[key].value.take()
    }

    pub fn get_or_insert_with<F: FnOnce() -> V>(&mut self, key: K, f: F) -> &mut V {
        self.0[key].value.get_or_insert_with(f)
    }
    
    pub fn iter_mut(&mut self) -> impl Iterator<Item=(K, &mut V)> {
        self.0.iter_mut().filter_map(|(key, value)| {
            value.value.as_mut().map(|val| (key, val))
        })
    }

    pub fn iter(&self) -> impl Iterator<Item=(K, &V)> {
        self.0.iter().filter_map(|(key, value)| {
            value.value.as_ref().map(|val| (key, val))
        })
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item=K> + 'static + use<K, V> {
        self.0.keys()
    }

    pub fn re_map<U>(&self) -> ArenaMap<K, U> {
        self.0.make_side_table()
    }

    pub fn fill_with(mut self, mut with: impl FnMut(K) -> V) -> FilledArenaMap<K, V> {
        for (key, meta) in self.0.iter_mut() {
            if meta.value.is_none() {
                meta.value = Some(with(key))
            }
        }
        FilledArenaMap(self)
    }
}

impl<K: Handle, V> Index<K> for ArenaMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index).expect("key should be initialized")
    }
}

impl<K: Handle, V> FilledArenaMap<K, V> {
    pub fn iter(&self) -> impl Iterator<Item=(K, &V)> {
        self.0.iter()
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item=K> + 'static + use<K, V> {
        self.0.keys()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K: Handle, V> Index<K> for FilledArenaMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        let arena: &Arena<_> = &self.0.0;
        // only constructed by filling another map
        // and always guarenteed to have all slots filled
        unsafe { arena[index].value.as_ref().unwrap_unchecked() }
    }
}

impl<K: Handle, V> IndexMut<K> for FilledArenaMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        let arena: &mut Arena<_> = &mut self.0.0;
        // only constructed by filling another map
        // and always guarenteed to have all slots filled
        unsafe { arena[index].value.as_mut().unwrap_unchecked() }
    }
}

pub struct SparseArenaMapBuilder<K, V> {
    raw: Vec<(HandleRaw, V)>,
    _marker: PhantomData<K>
}

impl<K: Handle, V> SparseArenaMapBuilder<K, V> {
    pub fn insert(&mut self, key: K, value: V) {
        self.raw.push((to_raw_handle(key), value))
    }

    pub fn build_in_place(&mut self) {
        self.raw.sort_unstable_by_key(|&(key, _)| key);
        self.raw.dedup_by_key(|&mut (key, _)| key);
    }
    
    pub fn build(mut self) -> SparseArenaMap<K, V> {
        self.build_in_place();
        SparseArenaMap(self)
    }
    
    fn unchecked_find(&self, key: K) -> Option<usize> {
        let key = to_raw_handle(key);
        let res = self.raw.binary_search_by(move |&(cmp_key, _)| {
            HandleRaw::cmp(&key, &cmp_key)
        });

        res.ok()
    }

    pub fn unchecked_get(&self, key: K) -> Option<&V> {
        let i = self.unchecked_find(key)?;
        Some(&self.raw[i].1)
    }

    pub fn unchecked_get_mut(&mut self, key: K) -> Option<&mut V> {
        let i = self.unchecked_find(key)?;
        Some(&mut self.raw[i].1)
    }

    pub fn len(&self) -> usize {
        self.raw.len()
    }

    pub fn get_at(&self, i: usize) -> Option<(K, &V)> {
        self.raw.get(i).map(|&(key, ref value)| (from_raw_handle(key), value))
    }
    
    pub fn iter(&self) -> impl Iterator<Item=(K, &V)> {
        self.raw.iter().map(|&(key, ref val)| (from_raw_handle(key), val))
    }
}

pub struct SparseArenaMap<K, V>(SparseArenaMapBuilder<K, V>);

impl<K: Handle, V> SparseArenaMap<K, V> {
    pub const fn builder() -> SparseArenaMapBuilder<K, V> {
        const {
            SparseArenaMapBuilder {
                raw: alloc::vec![],
                _marker: PhantomData,
            }
        }
    }

    pub fn get(&self, key: K) -> Option<&V> {
        self.0.unchecked_get(key)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.0.unchecked_get_mut(key)
    }
}


impl<K: Handle, V> Index<K> for SparseArenaMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index).expect("unknown key in sparse table")
    }
}

impl<K: Handle, V> IndexMut<K> for SparseArenaMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index).expect("unknown key in sparse table")
    }
}

#[repr(transparent)]
struct InternerObj<T: ?Sized + Internable>(T::StoredAs);

impl<T: ?Sized + Internable> InternerObj<T> {
    pub fn get_ref(&self) -> &T {
        self.0.borrow()
    }
}

impl<T: ?Sized + Internable> Storable for InternerObj<T> {
    type Handle = T::Handle;
}

unsafe impl<T: ?Sized + Internable> Constructable for InternerObj<T> {
    fn initial_vec() -> Vec<Self>
    where
        Self: Sized,
    {
        let vec: Vec<T::StoredAs> = <T as InternableStore>::initial_vec();
        unsafe {
            let (ptr, len, cap): (*mut T::StoredAs, usize, usize) = vec.into_raw_parts();
            Vec::from_raw_parts(ptr.cast::<InternerObj<T>>(), len, cap)
        }
    }
}

pub struct AnyInterner<T: ?Sized + Internable> {
    interned: Arena<InternerObj<T>>,
    hasher: hashed::Hasher,
    table: HashTable<T::Handle>,
}

impl<T: Debug + Internable> Debug for AnyInterner<T>
    where
        T::Handle: Debug
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f
            .debug_map()
            .entries(self.table.iter().map(|&handle| {
                let item: &T = self.interned[handle].get_ref();
                (item, handle)
            }))
            .finish()
    }
}

pub(crate) fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher
{
    hash_builder.hash_one(val)
}


pub(crate) unsafe fn make_hasher<'a, T, S>(
    hash_builder: &'a S,
    arena: &'a Arena<InternerObj<T>>
) -> impl Fn(&T::Handle) -> u64 + 'a
where
    T: ?Sized + Internable,
    S: BuildHasher
{
    move |&handle| {
        make_hash::<T, S>(
            hash_builder,
            (unsafe { arena.get_unchecked(handle) }).get_ref()
        )
    }
}

impl<T: ?Sized + Internable + 'static> AnyInterner<T> {
    pub fn new() -> Self {
        let arena = Arena::<InternerObj<T>>::new();
        let hasher = hashed::Hasher::default();
        let mut table = HashTable::new();
        for (handle, item) in arena.iter() {
            let hash = make_hash::<T, _>(&hasher, item.get_ref());
            let _entry = table.insert_unique(
                hash,
                handle,
                unsafe { make_hasher::<T, _>(&hasher, &arena) }
            );
        }

        Self {
            interned: arena,
            hasher,
            table,
        }
    }

    fn get_or_try_intern_inner<V>(
        &mut self,
        value: V,
        as_ref: impl FnOnce(&V) -> &T,
        into_obj: impl FnOnce(V) -> T::StoredAs,
    ) -> Option<T::Handle> {
        let item = as_ref(&value);
        let hash = make_hash(&self.hasher, &item);
        let interned = &self.interned;
        let entry = self.table.entry(
            hash,
            move |&key| {
                let val = (unsafe { interned.get_unchecked(key) }).get_ref();
                *val == *item
            },
            unsafe { make_hasher(&self.hasher, interned) }
        );

        let raw = match entry {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(slot) => {
                let (handle, sym_slot) = self.interned.try_reserve()?;
                let obj = into_obj(value);
                slot.insert(handle);
                sym_slot.insert(InternerObj(obj));
                handle
            }
        };

        Some(raw)
    }

    fn get_or_intern_inner<V>(
        &mut self,
        value: V,
        as_ref: impl FnOnce(&V) -> &T,
        into_obj: impl FnOnce(V) -> T::StoredAs,
    ) -> T::Handle {
        self.get_or_try_intern_inner(value, as_ref, into_obj)
            .unwrap_or_else(|| panic!("ran out of symbols"))
    }

    pub fn try_resolve(&self, symbol: T::Handle) -> Option<&T> {
        self.interned.get(symbol).map(InternerObj::get_ref)
    }

    pub fn resolve(&self, symbol: T::Handle) -> &T {
        self.try_resolve(symbol)
            .expect("symbols passed to resolve should come from the same interner")
    }

    pub fn len(&self) -> usize {
        self.interned.len()
    }

    pub fn make_side_table<V>(&self) -> ArenaMap<T::Handle, V> {
        self.interned.make_side_table()
    }


    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item=(T::Handle, &'a T)> + 'a + use<'a, T> {
        self.interned.iter().map(|(id, obj)| {
            (id, obj.get_ref())
        })
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item=T::Handle> {
        self.interned.keys()
    }
}

impl<T: Sized + Internable<StoredAs=T> + 'static> AnyInterner<T> {
    pub(crate) fn get_or_intern(&mut self, item: T) -> T::Handle {
        self.get_or_intern_inner(
            item,
            |x| x,
            core::convert::identity::<T>
        )
    }
}

impl<S: for<'a> From<&'a T>, T: ?Sized + Internable<StoredAs=S> + 'static> AnyInterner<T> {
    pub(crate) fn get_or_intern_ref(&mut self, item: &T) -> T::Handle {
        self.get_or_intern_inner(
            item,
            |x| *x,
            S::from
        )
    }
}

impl<T: Internable> Index<T::Handle> for AnyInterner<T> {
    type Output = T;

    fn index(&self, index: T::Handle) -> &Self::Output {
        self.resolve(index)
    }
}



pub struct IndexMap<K, V>(indexmap::IndexMap<K, V, hashed::Hasher>);

impl<K: Storable + Eq + Hash, V> IndexMap<K, V> {
    pub fn new() -> Self {
        Self(indexmap::IndexMap::default())
    }

    pub fn try_insert(&mut self, key: K, value: V) -> K::Handle {
        use indexmap::map::Entry;

        let raw_handle = match self.0.entry(key) {
            Entry::Occupied(occ) => {
                unsafe { HandleRaw::new(occ.index()).unwrap_unchecked() }
            },
            Entry::Vacant(empty) => {
                // make sure the handle is valid first **before** insertion
                let handle = HandleRaw::new(empty.index()).unwrap();
                empty.insert(value);
                handle
            }
        };

        from_raw_handle(raw_handle)
    }

    pub fn count(&self) -> HandleInt {
        unsafe { HandleRaw::usize_to_handle_int(self.0.len()).unwrap_unchecked() }
    }

    pub fn iter(&self) -> impl Iterator<Item=(K::Handle, &K, &V)> {
        self.0.iter().enumerate().map(|(i, (k, v))| {
            let handle = unsafe { HandleRaw::new(i).unwrap_unchecked() };
            (from_raw_handle(handle), k, v)
        })
    }

    pub fn get_indexed(&self, handle: K::Handle) -> (&K, &V) {
        self.0.get_index(handle.get()).unwrap()
    }
}



#[doc(hidden)]
macro_rules! make_handle_inner {
    (
        @to_unit $($tt:tt)*
    ) => {
        ()
    };

    (
        @filter {} $($tt:tt)*
    ) => {};

    (
        @filter {$($_tt:tt)+} $($tt:tt)*
    ) => {
        $($tt)*
    };

    (
        @not_filter {$($_tt:tt)+} $($tt:tt)*
    ) => {};

    (
        @not_filter {} $($tt:tt)*
    ) => {
        $($tt)*
    };

    (
        fold:
        $vis:vis $handle_name: ident for $ty: ty: $(! $({$not_sized: tt})?)? Sized;
        $(internable $({ InternAs = $intern_as: ty })?;)?
        $(with constants {
            {$($const_vis: vis $const: ident {$index: expr} = $value: expr;)*}
            {}
        })?
    ) => {
        $crate::arena::make_handle_raw!($vis $handle_name);

        /// # Safety
        /// all indicies constructed down bellow as a constant
        impl $crate::arena::Storable for $ty {
            type Handle = $handle_name;
        }

        unsafe impl $crate::arena::Constructable for $ty {
            $crate::arena::make_handle_inner! {
                @not_filter { $( ! $($not_sized)?)? }
                fn initial_vec() -> ::alloc::vec::Vec<Self> where Self: Sized {
                    ::alloc::vec![$($($value),*)?]
                }
            }
        }

        $crate::arena::make_handle_inner! {
            @not_filter { $( ! $($not_sized)?)? }
            $crate::arena::make_handle_inner! {
                @filter { $($($intern_as)?)? }
                compile_error!("sized structs can't be interned as anything other than themselves");
            }
            $crate::arena::make_handle_inner! {
                @filter { $( internable $($intern_as)?)? }
                impl $crate::arena::InternableSimple for $ty {}
            }
        }

        $crate::arena::make_handle_inner! {
            @filter { $( ! $($not_sized)?)? }
            $crate::arena::make_handle_inner! {
                @not_filter { $($($intern_as)?)? }
                compile_error!("unsized structs need to be interned as something");
            }
            // Safety: Constructable doesn't even have an initial vec impl in this case
            //         since $ty: Sized
            unsafe impl $crate::arena::InternableStore for $ty {
                type StoredAs = $($($intern_as)?)?;

                fn initial_vec() -> ::alloc::vec::Vec<Self::StoredAs> {
                    ::alloc::vec![$($($value),*)?]
                }
            }
        }



        impl $handle_name {
            $($(
            #[allow(dead_code)]
            $const_vis const $const: Self = Self::new($index).unwrap();
            )*)?
        }



        $(const _: usize = {
            let mut counter: usize = 0;

            $(
            #[allow(non_snake_case)]
            {
                let $const = counter;
                assert!($const == $index);
            }

            counter = counter.checked_add(1).unwrap();
            )*
            counter
        };)?



        $crate::arena::make_handle_inner! {
            @filter { $( internable $($intern_as)?)? }
            #[cfg(test)]
            pastey::paste! {
                mod [<test_ $handle_name:snake _interner>] {
                    #[test]
                    fn [<test_$handle_name:snake>]() {
                        $(
                        use super::*;
                        let interner = $crate::arena::AnyInterner::<$ty>::new();

                        $(
                        {
                            assert_eq!(*interner.resolve($handle_name::$const), $value);
                        }
                        )*
                        let _ = interner;
                        )?
                    }
                }
            }
        }
    };

    (
        fold:
        $vis:vis $handle_name: ident for $ty: ty: $(! $({$not_sized: tt})?)? Sized;
        $(internable $({ InternAs = $intern_as: ty })?;)?
        $(with constants {
            {$($resolved_const_vis: vis $resolved_const: ident {$index: expr} = $resolved_value: expr;)*}
            {
            $processing_const_vis: vis $processing_const: ident = $preocessing_value: expr;
            $($const_vis: vis $const: ident = $value: expr;)*
            }
        })?
    ) => {
        $crate::arena::make_handle_inner! {
            fold:
            $vis $handle_name for $ty: $(! $({$not_sized})?)? Sized;
            $(internable $({ InternAs = $intern_as })?;)?
            $(with constants {
                {
                    $($resolved_const_vis $resolved_const {$index} = $resolved_value;)*
                    $processing_const_vis $processing_const {
                        <[()]>::len(&[
                            $($crate::arena::make_handle_inner!(@to_unit $resolved_const)),*
                        ])
                    } = $preocessing_value;
                }
                {$($const_vis $const = $value;)*}
            })?
        }
    }
}


macro_rules! make_handle {
    (
        $vis:vis $handle_name: ident for $ty: ty: $(! $({$not_sized: tt})?)? Sized;
        $(internable $({ InternAs = $intern_as: ty })?;)?
        $(with constants {
            $($const_vis: vis $const: ident = $value: expr;)*
        })?
    ) => {
        $crate::arena::make_handle_inner! {
            fold:
            $vis $handle_name for $ty: $(! $({$not_sized})?)? Sized;
            $(internable $({ InternAs = $intern_as })?;)?
            $(with constants {
                {  }
                {$($const_vis $const = $value;)*}
            })?
        }
    }
}

macro_rules! make_handle_raw {
    ($vis:vis $handle_name: ident) => {
        #[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
        #[repr(transparent)]
        $vis struct $handle_name($crate::arena::HandleRaw);

        #[allow(dead_code)]
        impl ::core::fmt::Debug for $handle_name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f
                    .debug_tuple(stringify!($handle_name))
                    .field(&self.get())
                    .finish()
            }
        }

        unsafe impl $crate::arena::Handle for $handle_name {}

        impl $handle_name {
            /// # Note
            /// a valid handle can point to this
            /// there is no way to check if a handle is invalid
            /// as
            #[doc = concat!("`handle == ", stringify!($handle_name), "::INVALID`")]
            /// can return true even for a valid handle
            #[allow(dead_code, reason = "macro generated code")]
            $vis const INVALID: Self = Self($crate::arena::HandleRaw::MAX);

            #[inline(always)]
            #[allow(dead_code, reason = "macro generated code")]
            $vis const fn new(handle: usize) -> Option<Self> {
                match $crate::arena::HandleRaw::new(handle) {
                    Some(x) => Some(Self(x)),
                    None => None,
                }
            }


            #[allow(dead_code, reason = "macro generated code")]
            #[inline(always)]
            pub(crate) const fn as_handle_count(self) -> $crate::arena::HandleInt {
                self.0.as_handle_int()
            }

            #[allow(dead_code, reason = "macro generated code")]
            #[inline(always)]
            $vis const fn get(self) -> usize {
                self.0.get()
            }
        }
    }
}

#[doc(hidden)]
#[allow(unused_imports)]
pub(crate) use make_handle_inner;

pub(crate) use {make_handle, make_handle_raw};
use crate::hashed;
