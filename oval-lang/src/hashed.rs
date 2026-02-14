pub(crate) type Hasher = foldhash::fast::RandomState;
pub(crate) type HashSet<T> = hashbrown::HashSet<T, Hasher>;
pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, Hasher>;
pub(crate) type HashTable<T> = hashbrown::HashTable<T>;
pub(crate) type PersistentHashMap<K, V> = rpds::HashTrieMap<K, V, archery::RcK, Hasher>;

macro_rules! ph_map {
    {} => {
        $crate::hashed::PersistentHashMap::new_with_hasher_and_ptr_kind(
            $crate::hashed::Hasher::default()
        )
    };
    {$($k:expr => $v:expr),+ $(,)?} => {{
        let mut map = $crate::hashed::ph_map! { };
        $(map.insert_mut($k, $v);)+
        map
    }};
}

pub(crate) use ph_map;
