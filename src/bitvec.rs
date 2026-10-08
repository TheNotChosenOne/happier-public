use crate::{unchecked_get, unchecked_mut};
use alloc::vec::Vec;

#[cfg_attr(feature = "serde", derive(bincode::Encode, bincode::Decode))]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BitVec {
    words: Vec<u64>,
}

impl BitVec {
    pub fn new() -> Self {
        BitVec { words: Vec::new() }
    }

    pub fn resize(&mut self, size: usize) {
        let num_words = size.div_ceil(64);
        self.words.resize(num_words, 0);
    }

    #[inline(always)]
    pub fn any(&self) -> Option<usize> {
        if let Some(word) = self.words.iter().copied().position(|w| w != 0) {
            let bit = self.words[word].trailing_zeros() as usize;
            Some(word * 64 + bit)
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn contains(&self, index: usize) -> bool {
        let word_index = index / 64;
        let bit_index = index % 64;
        debug_assert!(word_index < self.words.len());
        (unchecked_get(&self.words, word_index) & (1 << bit_index)) != 0
    }

    #[inline(always)]
    pub fn insert(&mut self, index: usize) {
        debug_assert!(!self.contains(index));
        let word_index = index / 64;
        let bit_index = index % 64;
        *unchecked_mut(&mut self.words, word_index) |= 1 << bit_index;
    }

    #[inline(always)]
    pub fn remove(&mut self, index: usize) {
        debug_assert!(self.contains(index));
        let word_index = index / 64;
        let bit_index = index % 64;
        *unchecked_mut(&mut self.words, word_index) &= !(1 << bit_index);
    }
}
