use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "mem_dbg")]
use mem_dbg::{MemDbg, MemSize};

type Block = u64;
const BLOCK_SIZE: u64 = Block::BITS as u64;

const fn bit_to_block(b: bool) -> Block {
    if b {
        !0
    } else {
        0
    }
}

/// Scale bit-length to block-length, rounded up to the next block.
const fn len_to_blocks(len: u64) -> u64 {
    (len + BLOCK_SIZE - 1) / BLOCK_SIZE
}

#[macro_export]
macro_rules! bit_arr {
    () => (
        $crate::BitArray::new()
    );
    ($b:expr; $n:expr) => (
        $crate::BitArray::from_bit($b, $n)
    );
    ($($b:expr),+ $(,)?) => (
        $crate::BitArray::from([$($b),+].as_slice())
    );
}

#[derive(Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "mem_dbg", derive(MemDbg, MemSize))]
pub struct BitArray {
    blocks: Vec<Block>,
}

impl BitArray {
    /// Constructs a new, empty [`BitArray`].
    ///
    /// The array will not allocate until bits are set.
    pub fn new() -> Self {
        BitArray { blocks: Vec::new() }
    }

    pub fn from_bit(b: bool, len: u64) -> Self {
        let n_blocks = len_to_blocks(len);
        BitArray {
            blocks: vec![bit_to_block(b); n_blocks as usize],
        }
    }

    pub fn with_capacity(capacity: u64) -> Self {
        let n_blocks = len_to_blocks(capacity);
        BitArray {
            blocks: Vec::with_capacity(n_blocks as usize),
        }
    }

    pub fn with_word_capacity(word_size: u64, capacity: u64) -> Self {
        BitArray::with_capacity(word_size * capacity)
    }

    /// Returns the number of bits in the array.
    pub fn len(&self) -> u64 {
        self.blocks.len() as u64 * BLOCK_SIZE
    }

    /// Returns the number of bits the array can hold without reallocating.
    pub fn capacity(&self) -> u64 {
        self.blocks.capacity() as u64 * BLOCK_SIZE
    }

    /// Sets the bit at position `i` to `b`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut ba = fid::BitArray::from_bit(false, 8);
    /// ba.set_bit(3, true);
    /// assert_eq!(ba.get_bit(3), true);
    /// assert_eq!(ba.get_bit(4), false);
    /// ba.set_bit(256, true);  // automatically extended
    /// assert_eq!(ba.get_bit(256), true);
    /// ```
    pub fn set_bit(&mut self, i: u64, b: bool) {
        if i >= self.len() {
            self.resize(i + 1, false);
        }

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let mask = 1 << p;
        let value = (b as Block) << p;

        let slot = &mut self.blocks[k as usize];
        *slot = (*slot & !mask) | value;
    }

    /// Gets the bit at position `i`.
    ///
    /// # Panics
    /// Panics if the specified position exceeds the capacity.
    pub fn get_bit(&self, i: u64) -> bool {
        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;

        (self.blocks[k as usize] >> p) & 0b1 == 1
    }

    /// Sets the slice of size `slice_size` at position `i`.
    ///
    /// # Panics
    /// Panics if `slice_size` is greater than 64.
    pub fn set_slice(&mut self, i: u64, slice_size: u64, slice: u64) {
        debug_assert!(slice_size <= 64);
        if slice_size == 0 {
            return;
        }
        if i + slice_size > self.len() {
            self.resize(i + slice_size, false);
        }

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let excess = (i + slice_size).saturating_sub((k + 1) * BLOCK_SIZE);

        let mask1 = slice << p;
        self.blocks[k as usize] |= mask1;
        if excess != 0 {
            let mask2 = (slice >> (BLOCK_SIZE - p)) & (!0 >> (BLOCK_SIZE - excess));
            self.blocks[k as usize + 1] |= mask2;
        }
    }

    /// Sets the `i`-th word of size `word_size` to `word`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut ba = fid::BitArray::new();
    /// ba.set_word(0, 12, 0b0101_1010_1100);
    /// assert_eq!(ba.get_word(0, 12), 0b0101_1010_1100);
    /// ba.set_word(5, 12, 0b1010_0101_0011);
    /// assert_eq!(ba.get_word(5, 12), 0b1010_0101_0011);
    /// ```
    #[inline]
    pub fn set_word(&mut self, i: u64, word_size: u64, word: u64) {
        self.set_slice(i * word_size, word_size, word);
    }

    /// Gets the slice of size `slice_size` at position `i`.
    ///
    /// # Panics
    /// Panics if the end position of the slice exceeds the capacity or `slice_size` is greater than 64.
    pub fn get_slice(&self, i: u64, slice_size: u64) -> u64 {
        debug_assert!(slice_size <= 64);
        debug_assert!(i + slice_size <= self.len());

        if slice_size == 0 {
            return 0;
        }

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let excess = (i + slice_size).saturating_sub((k + 1) * BLOCK_SIZE);
        let w1 = (self.blocks[k as usize] >> p) & (!0 >> (BLOCK_SIZE - slice_size));
        if excess == 0 {
            w1
        } else {
            let w2 = self.blocks[k as usize + 1] & (!0 >> (BLOCK_SIZE - excess));
            w1 | w2 << (BLOCK_SIZE - p)
        }
    }

    /// Gets the `i`-th word of size `word_size`.
    pub fn get_word(&self, i: u64, word_size: u64) -> u64 {
        self.get_slice(i * word_size, word_size)
    }

    /// Resizes the array in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the array is extended by the difference, with each additional slot filled with `b`.
    /// If `new_len` is less than `len`, the array is simply truncated.
    #[cold]
    pub fn resize(&mut self, new_len: u64, b: bool) {
        self.blocks
            .resize(len_to_blocks(new_len) as usize, bit_to_block(b));
    }
}

impl fmt::Debug for BitArray {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.blocks
            .iter()
            .map(|b| writeln!(f, "{:0w$b}", b, w = BLOCK_SIZE as usize))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_word_get_word() {
        let word_size = 7;
        let mut ba = bit_arr![false; word_size * 128];
        for i in 0..128 {
            ba.set_word(i, word_size, i as u64);
        }
        for i in 0..128 {
            assert_eq!(ba.get_word(i, word_size), i as u64);
        }
    }

    #[test]
    fn set_bit_get_word() {
        let points = &[3, 5, 6, 7];
        let mut ba = bit_arr![false; 8];
        for &p in points {
            ba.set_bit(p, true);
        }
        assert_eq!(ba.get_word(0, 4), 8);
        assert_eq!(ba.get_word(1, 4), 14);
    }

    #[test]
    fn set_bit_get_bit() {
        let mut ba = bit_arr![false; 256];
        let points = &[2, 3, 5, 8, 13, 21, 34, 55, 89, 144];

        for &p in points {
            ba.set_bit(p, true);
        }

        let mut j = 0;
        for i in 0..145 {
            if i == points[j] {
                assert_eq!(ba.get_bit(i), true);
                j += 1;
            } else {
                assert_eq!(ba.get_bit(i), false);
            }
        }
    }

    #[test]
    fn extend_with_resize() {
        let mut ba = bit_arr![false; BLOCK_SIZE * 4];
        assert_eq!(ba.blocks.len(), 4);
        ba.resize(BLOCK_SIZE * 5, false);
        assert_eq!(ba.blocks.len(), 5);
        ba.resize(BLOCK_SIZE * 6 + 7, false);
        assert_eq!(ba.blocks.len(), 7);
    }

    #[test]
    fn shrink_with_resize() {
        let mut ba = bit_arr![false; BLOCK_SIZE * 4];
        assert_eq!(ba.blocks.len(), 4);
        ba.resize(BLOCK_SIZE * 3, false);
        assert_eq!(ba.blocks.len(), 3);
        ba.resize(BLOCK_SIZE + 3, false);
        assert_eq!(ba.blocks.len(), 2);
    }
}
