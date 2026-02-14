use alloc::boxed::Box;
use core::fmt::{Debug, Formatter};

pub type InnerWord = usize;

const WORD_BITS: usize = {
    let bits: u32 = InnerWord::BITS;
    match u32::BITS > usize::BITS {
        true => {
            // widening cast since u32 has more bits than usize
            let max = usize::MAX as u32;
            assert!(bits <= max);
            // truncating cast but bits is less than the maximum; no truncation happens
            max as usize
        },
        // widening cast since usize has more bits than u32
        false => bits as usize
    }
};

pub struct BitSet(Box<[InnerWord]>);

#[inline]
const fn bit_index(index: usize) -> (usize, usize) {
    (index / WORD_BITS, index % WORD_BITS)
}

impl BitSet {
    pub fn new(len: usize) -> Self {
        Self(crate::alloc_helper::zeroed_slice::<InnerWord>(len.div_ceil(WORD_BITS)))
    }

    pub fn get(&self, idx: usize) -> bool {
        let (word_index, bit_index) = bit_index(idx);
        (self.0[word_index] & (1 << bit_index)) != 0
    }

    pub fn set(&mut self, idx: usize) {
        let (word_index, bit_index) = bit_index(idx);
        self.0[word_index] |= 1 << bit_index
    }
}

impl Debug for BitSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let len = self.0.len() * WORD_BITS;
        f.debug_list().entries((0..len).map(|i| self.get(i))).finish()
    }
}