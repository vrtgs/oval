use crate::compile::hir::IndirectTyId;
use alloc::vec;
use alloc::vec::Vec;

pub(super) struct UnificationTableBuilder {
    // invariant parents.len() == ranks.len()
    parents: Vec<IndirectTyId>,
    ranks: Vec<u8>,
}

//     full path compression if needed
//     let mut x = id;
//     while parents[x.get()] != x {
//         x = parents[x.get()];
//     }
//     let root = x;
//
//     // pass 2: compress
//     let mut x = id;
//     while parents[x.get()] != x {
//         let next = parents[x.get()];
//         parents[x.get()] = root;
//         x = next;
//     }
//     root

unsafe fn find_slice(parents: &mut [IndirectTyId], mut id: IndirectTyId) -> IndirectTyId {
    if parents.get(id.get()).is_none() {
        return id;
    }

    unsafe {
        while let i = id.get() && let parent = *parents.get_unchecked(i) && parent != id {
            let halved = *parents.get_unchecked(parent.get());
            *parents.get_unchecked_mut(i) = halved;
            id = halved;
        }
    }

    id
}

impl UnificationTableBuilder {
    pub fn new() -> Self {
        const {
            Self {
                parents: vec![],
                ranks: vec![]
            }
        }
    }

    fn assert_invariant(&self) {
        unsafe { core::hint::assert_unchecked(self.parents.len() == self.ranks.len()) }
    }

    fn ensure_space(&mut self, max_id: IndirectTyId) {
        self.assert_invariant();
        struct Guard<'a> {
            original_len: usize,
            parents: &'a mut Vec<IndirectTyId>,
            ranks: &'a mut Vec<u8>,
        }

        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.parents.truncate(self.original_len);
                self.ranks.truncate(self.original_len);
            }
        }

        let len = max_id.get().checked_add(1).unwrap_or_else(|| {
            panic!("capacity overflow")
        });

        if len <= self.parents.len() {
            return;
        }

        let mut index = self.parents.len();
        let guard = Guard {
            original_len: index,
            parents: &mut self.parents,
            ranks: &mut self.ranks
        };
        guard.parents.resize_with(len, || {
            let id = unsafe { IndirectTyId::new(index).unwrap_unchecked() };
            index += 1;
            id
        });

        guard.ranks.resize(len, 0);

        core::mem::forget(guard);

        self.assert_invariant();
    }

    pub fn find(&mut self, id: IndirectTyId) -> IndirectTyId {
        unsafe { find_slice(&mut self.parents, id) }
    }

    pub fn union_known_roots(&mut self, mut root_a: IndirectTyId, mut root_b: IndirectTyId) {
        if root_a == root_b {
            return;
        }

        self.ensure_space(root_a);
        self.ensure_space(root_b);

        let rank_a = self.ranks[root_a.get()];
        let rank_b = self.ranks[root_b.get()];
        if rank_a < rank_b {
            core::mem::swap(&mut root_a, &mut root_b);
        } else if rank_a == rank_b && root_a > root_b {
            core::mem::swap(&mut root_a, &mut root_b);
        }

        self.parents[root_b.get()] = root_a;
        if rank_a == rank_b {
            #[cold]
            fn rank_overflow() -> ! {
                unreachable!("\
                since Id's only go up to 2^32 \
                and for the rank to overflow there needs to be 2^255 nodes \
                this is impossible\
                ")
            }

            self.ranks[root_a.get()] = rank_a.checked_add(1).unwrap_or_else(|| {
                rank_overflow()
            });
        }
    }

    // pub fn build(self) -> UnificationTable {
    //     let mut parents = self.parents.into_boxed_slice();
    //
    //     // Fully path-compress so every stored id maps directly to its root.
    //     for i in 0..parents.len() {
    //         // SAFETY: self only grows by passing in a valid TyId
    //         // so all indicied of parent corrispont to valid type ids
    //         let id = unsafe { TyId::new(i).unwrap_unchecked() };
    //         let root = unsafe { find_slice(&mut parents, id) };
    //         parents[i] = root;
    //     }
    //
    //     UnificationTable { parents }
    // }
}


// pub(crate) struct UnificationTable {
//     parents: Box<[TyId]>,
// }
//
// impl UnificationTable {
//     pub fn find(&self, id: TyId) -> TyId {
//         self.parents.get(id.get()).copied().unwrap_or(id)
//     }
// }