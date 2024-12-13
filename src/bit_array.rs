use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "mem_dbg")]
use mem_dbg::{MemDbg, MemSize};

use crate::util::mask_u64;

type Block = u64;
const BLOCK_SIZE: u64 = Block::BITS as u64;

const fn splat_bit_to_block(b: bool) -> Block {
    if b {
        !0
    } else {
        0
    }
}

/// Scale bit-length to block-length, rounded up to the next block.
fn blocks_for_bits(len: u64) -> usize {
    usize::try_from((len + BLOCK_SIZE - 1) / BLOCK_SIZE).unwrap()
}

fn pack_block(slice: &[bool]) -> Block {
    debug_assert!(slice.len() <= Block::BITS as usize);
    slice
        .into_iter()
        .enumerate()
        .fold(0, |acc, (i, b)| acc | (*b as Block) << i)
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
    // TODO: don't use Vec; we don't need to track both cap and len
    blocks: Vec<Block>,
}

impl BitArray {
    /// Constructs a new, empty [`BitArray`].
    ///
    /// The array will not allocate until bits are set.
    pub fn new() -> Self {
        BitArray { blocks: Vec::new() }
    }

    /// Constructs a new [`BitArray`] with `len` (rounded up to blocks).
    ///
    /// Each block is set to `value`. The last block is not masked to match `len`.
    pub fn from_block(value: Block, len: u64) -> Self {
        let block_len = blocks_for_bits(len);
        let blocks = vec![value; block_len];

        BitArray { blocks }
    }

    /// Constructs a new [`BitArray`] with `len` bits set to `b`.
    ///
    /// The last block is masked to match `len`.
    pub fn from_bit(b: bool, len: u64) -> Self {
        let block_len = blocks_for_bits(len);
        let mut blocks = vec![splat_bit_to_block(b); block_len];

        let excess = len % BLOCK_SIZE;
        if b && excess != 0 {
            if let Some(last) = blocks.last_mut() {
                *last &= mask_u64(excess);
            }
        }
        BitArray { blocks }
    }

    pub fn with_capacity(capacity: u64) -> Self {
        let block_len = blocks_for_bits(capacity);
        BitArray {
            blocks: Vec::with_capacity(block_len),
        }
    }

    pub fn with_word_capacity(word_size: u64, capacity: u64) -> Self {
        BitArray::with_capacity(word_size * capacity)
    }

    /// Returns the number of blocks in the array.
    pub fn block_len(&self) -> usize {
        self.blocks.len()
    }

    /// Returns the number of bits in the array.
    pub fn len(&self) -> u64 {
        self.block_len() as u64 * BLOCK_SIZE
    }

    /// Returns the number of blocks the array can hold without reallocating.
    pub fn block_capacity(&self) -> usize {
        self.blocks.capacity()
    }

    /// Returns the number of bits the array can hold without reallocating.
    pub fn capacity(&self) -> u64 {
        self.block_capacity() as u64 * BLOCK_SIZE
    }

    /// Shrinks the capacity of the array as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.blocks.shrink_to_fit();
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
        self.ensure_bit_len(i + 1);

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let mask = 1 << p;
        let value = (b as Block) << p;

        // SAFETY: `ensure_bit_len()` ensures valid len
        unsafe { self.set_block_unchecked(k as usize, value, mask) }
    }

    /// Gets the bit at position `i`.
    ///
    /// # Panics
    /// * Position `i` exceeds the capacity.
    pub fn get_bit(&self, i: u64) -> bool {
        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;

        (self.blocks[k as usize] >> p) & 0b1 == 1
    }

    /// Sets the slice of size `size` at position `i`.
    ///
    /// # Panics
    /// * `size` is greater than 64.
    pub fn set_slice(&mut self, i: u64, size: u64, slice: u64) {
        debug_assert!(size <= 64);
        if size == 0 {
            return;
        }
        self.ensure_bit_len(i + size);

        // SAFETY: `ensure_bit_len()` ensures valid len
        unsafe { self.set_slice_unchecked(i, size, slice) }
    }

    /// Mutate [`blocks`] without bound checks.
    #[inline]
    unsafe fn set_slice_unchecked(&mut self, i: u64, size: u64, slice: u64) {
        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;

        self.set_block_unchecked(k as usize, slice << p, mask_u64(size) << p);

        let excess = (i + size).saturating_sub((k + 1) * BLOCK_SIZE);
        if excess != 0 {
            self.set_block_unchecked(k as usize + 1, slice >> (BLOCK_SIZE - p), mask_u64(excess));
        }
    }

    /// Mutate [`blocks`] without bound checks.
    ///
    /// [`blocks`]: BitArray::blocks
    #[inline(always)]
    unsafe fn set_block_unchecked(&mut self, k: usize, bits: u64, mask: u64) {
        debug_assert!(k < self.blocks.len());

        let slot = self.blocks.get_unchecked_mut(k);
        *slot = (*slot & !mask) | bits;
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

    /// Sets the `slice` at position `i`.
    pub fn set_bit_slice(&mut self, i: u64, slice: &[bool]) {
        let new_len = i + slice.len() as u64;
        self.ensure_bit_len(new_len);

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let mid = BLOCK_SIZE - p;

        // SAFETY: `ensure_bit_len()` ensures valid len
        unsafe {
            let tail = if let Some((head, slice)) = slice.split_at_checked(mid as usize) {
                let chunks = slice.chunks_exact(BLOCK_SIZE as usize);
                let tail = chunks.remainder();

                self.set_slice_unchecked(i, head.len() as u64, pack_block(head));

                let view = self.blocks.get_unchecked_mut(k as usize + 1..);
                debug_assert!(chunks.len() <= view.len());

                for (i, chunk) in chunks.enumerate() {
                    *view.get_unchecked_mut(i) = pack_block(chunk);
                }

                tail
            } else {
                slice
            };

            self.set_slice_unchecked(
                new_len - tail.len() as u64,
                tail.len() as u64,
                pack_block(tail),
            );
        }
    }

    /// Gets a slice with `size` bits at position `i`.
    ///
    /// # Panics
    /// * End position of the slice exceeds the capacity.
    /// * `size` is greater than 64.
    pub fn get_slice(&self, i: u64, size: u64) -> u64 {
        debug_assert!(size <= 64);
        assert!(i + size <= self.len());

        if size == 0 {
            return 0;
        }

        let k = i / BLOCK_SIZE;
        let p = i % BLOCK_SIZE;
        let excess = (i + size).saturating_sub((k + 1) * BLOCK_SIZE);

        // SAFETY: `i + size` assert
        let bits = unsafe {
            let w1 = *self.blocks.get_unchecked(k as usize) >> p;
            if excess == 0 {
                w1
            } else {
                let w2 = *self.blocks.get_unchecked(k as usize + 1);
                w1 | (w2 << (BLOCK_SIZE - p))
            }
        };

        bits & mask_u64(size)
    }

    /// Gets the `i`-th word with `size` bits.
    ///
    /// # Panics
    /// * End position of the word exceeds the capacity.
    /// * `size` is greater than 64.
    pub fn get_word(&self, i: u64, size: u64) -> u64 {
        self.get_slice(i * size, size)
    }

    /// Reserves capacity for at least `additional` more bits (rounded up to blocks).
    ///
    /// See [`reserve_blocks`] for details.
    ///
    /// [`reserve_blocks`]: BitArray::reserve_blocks
    pub fn reserve(&mut self, additional: u64) {
        self.blocks.reserve(blocks_for_bits(additional));
    }

    /// Reserves capacity for at least `additional` more blocks.
    ///
    /// * May reserve more space to speculatively avoid frequent reallocations.
    /// * Capacity will become greater than or equal to `self.len() + additional`.
    /// * Does nothing if capacity is already sufficient.
    pub fn reserve_blocks(&mut self, additional: usize) {
        self.blocks.reserve(additional);
    }

    /// Reserves capacity for at least `additional` more bits (rounded up to blocks).
    ///
    /// See [`reserve_exact_blocks`] for details.
    ///
    /// [`reserve_exact_blocks`]: BitArray::reserve_exact_blocks
    pub fn reserve_exact(&mut self, additional: u64) {
        self.blocks.reserve_exact(blocks_for_bits(additional));
    }

    /// Reserves capacity for at least `additional` more blocks.
    ///
    /// * Unlike [`reserve`], this will not deliberately over-allocate to speculatively avoid frequent allocations.
    /// * Capacity will become greater than or equal to `self.len() + additional`
    ///   (the allocator may give more space than requested).
    /// * Does nothing if the capacity is already sufficient.
    ///
    /// [`reserve`]: BitArray::reserve
    pub fn reserve_exact_blocks(&mut self, additional: usize) {
        self.blocks.reserve_exact(additional);
    }

    /// Resizes the array in-place so that `len` is at least `new_len` (rounded up to blocks).
    ///
    /// See [`resize_blocks`] for details.
    ///
    /// [`resize_blocks`]: BitArray::resize_blocks
    pub fn resize(&mut self, new_len: u64, b: bool) {
        self.resize_blocks(blocks_for_bits(new_len), splat_bit_to_block(b));
    }

    /// Resizes the array in-place so that `len` is equal to `new_len`.
    ///
    /// * If `new_len` is greater than `len`, the array is extended by the difference,
    ///   with additional blocks equal to `value`.
    /// * If `new_len` is less than `len`, the array is truncated.
    pub fn resize_blocks(&mut self, new_len: usize, value: Block) {
        self.blocks.resize(new_len, value);
    }

    /// Shortens the array, keeping the first `new_len` bits (rounded up to blocks) and dropping the rest.
    ///
    /// See [`truncate_blocks`] for details.
    ///
    /// [`truncate_blocks`]: BitArray::truncate_blocks
    pub fn truncate(&mut self, new_len: u64) {
        self.truncate_blocks(blocks_for_bits(new_len));
    }

    /// Shortens the array, keeping the first `new_len` blocks and dropping the rest.
    ///
    /// * If `new_len` is greater or equal to `len`, this has no effect.
    /// * This has no effect on the allocated capacity.
    pub fn truncate_blocks(&mut self, new_len: usize) {
        self.blocks.truncate(new_len);
    }

    fn ensure_bit_len(&mut self, len: u64) {
        if len > self.len() {
            resize_cold(self, len);
        }

        #[cold]
        fn resize_cold(_self: &mut BitArray, new_len: u64) {
            _self.resize(new_len, false);
        }
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

impl From<&[bool]> for BitArray {
    fn from(value: &[bool]) -> Self {
        let mut arr = Self::new();
        arr.set_bit_slice(0, value);
        arr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn get_empty_slice_panic() {
        let ba = bit_arr![false; 128];
        ba.get_slice(129, 0);
    }

    #[test]
    fn set_and_get_empty_slice() {
        let mut ba = bit_arr![false; 128];
        for i in 0..128 {
            ba.set_slice(i, 0, 0);
        }
        for i in 0..128 {
            assert_eq!(ba.get_slice(i, 0), 0);
        }
    }

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

    #[test]
    fn init_from_bools() {
        let slice = &mut [false; 128];
        for i in 0..slice.len() {
            slice[i] = i % 3 == 0;
        }

        let mut arr = BitArray::new();
        arr.set_bit_slice(1, slice);

        assert_eq!(arr.get_bit(0), false);
        for i in 1..slice.len() {
            assert_eq!(arr.get_bit(i as u64), slice[i - 1]);
        }
    }
}
