use crate::bit_array::*;
use crate::coding::*;
use crate::fid::FID;
use crate::fid_iter::FidBitIter;
use crate::util::{mask_u64, phi_sub};
use std::hint::black_box;
use std::num::NonZeroU32;
use std::ops::Index;

use roxygen::*;

const SBLOCK_SIZE: u64 = 7; // ceil(log(SBLOCK_SIZE + 1))
const LBLOCK_WIDTH: u64 = 1024;
const LBLOCK_SIZE: u64 = 10;
const SELECT_UNIT_NUM: u64 = 4096;

#[macro_export]
macro_rules! bit_vec {
    () => (
        $crate::BitVector::new()
    );
    ($b:expr; $n:expr) => (
        $crate::BitVector::from_bit($b, $n)
    );
    ($($b:expr),+ $(,)?) => (
        $crate::BitVector::from([$($b),+].as_slice())
    );
}

/// A succinct bit vector that supports FID operations (rank and select) in constant time.
///
/// Bits are divided in small and large blocks. Each small block is identified by
/// a class (number of 1s in the block) and an index within the class.
/// Classes are stored in `ceil(log(SBLOCK_WIDTH + 1))` bits.
/// Indices are stored in `log(C(SBLOCK_WIDTH, index))` bits with enumerative code
/// if its compressed size is less than `MAX_CODE_SIZE`. Otherwise the bit pattern
/// of the small block is explicitly stored as an index for the sake of efficiency.
/// This idea originally comes from [2]. For each large block, we store the number
/// of 1s up to its beginning and a pointer for the index of the first small block.
///
/// # Examples
///
/// ```
/// # use fid::{bit_vec, FID};
/// // 01101101
/// let mut bv = bit_vec![false, true, true, false, true, true, false, true];
/// assert_eq!(bv.rank0(5), 2);
/// assert_eq!(bv.rank1(5), 3);
/// assert_eq!(bv.select0(2), 6);
/// assert_eq!(bv.select1(2), 4);
/// ```
///
/// # References
/// [1] Gonzalo Navarro and Eliana Providel. 2012. Fast, small, simple rank/select on bitmaps.
/// In Proceedings of the 11th international conference on Experimental Algorithms (SEA'12),
/// Ralf Klasing (Ed.). Springer-Verlag, Berlin, Heidelberg, 295-306.
/// DOI=http://dx.doi.org/10.1007/978-3-642-30850-5_26
///
/// [2] rsdic by Daisuke Okanohara.
/// [https://github.com/hillbig/rsdic](https://github.com/hillbig/rsdic)
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "mem_dbg", derive(mem_dbg::MemDbg, mem_dbg::MemSize))]
pub struct BitVector {
    /// Length of the vector (number of bits).
    len: u64,
    /// Number of 1s.
    ones: u64,
    /// Class identifiers (number of 1s) of small blocks of width `SBLOCK_WIDTH`,
    /// which are represented with `SBLOCK_SIZE` bits.
    sblocks: BitArray,
    /// Rank1 (number of 1s) up to the i-th super block.
    lblocks: Vec<u64>,
    /// Indices of each small block.
    indices: BitArray,
    /// Pointers to `indices`.
    pointers: Vec<u64>,

    select1_unit_pointers: Vec<usize>,
    select0_unit_pointers: Vec<usize>,

    last_sblock_bits: u64,
    pointer: u64,
}

impl BitVector {
    /// Constructs a new, empty [`BitVector`].
    ///
    /// The vector will not allocate until elements are pushed onto it.
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> FidBitIter<'_, Self> {
        FidBitIter::new(&self)
    }

    pub fn to_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }

    pub fn from_bit(b: bool, len: u64) -> Self {
        let true_odds = (b as u8) as f64;
        let false_odds = (!b as u8) as f64;
        let mut vec = Self::with_odds_and_code_size(len, true_odds, false_odds, 0);
        for _ in 0..len {
            vec.push(b);
        }
        vec
    }

    fn with_odds_and_code_size(
        capacity: u64,
        true_odds: f64,
        false_odds: f64,
        code_size: u32,
    ) -> Self {
        if capacity == 0 {
            return Self::new();
        }

        let sblock_len = capacity.div_ceil(SBLOCK_WIDTH);
        let lblock_len = capacity.div_ceil(LBLOCK_WIDTH) as usize;

        let select_units = capacity.div_ceil(SELECT_UNIT_NUM) as f64;
        let predicted_one_units = (select_units * true_odds).ceil() as usize;
        let predicted_zero_units = (select_units * false_odds).ceil() as usize;

        BitVector {
            len: 0,
            ones: 0,
            sblocks: BitArray::with_capacity(sblock_len * SBLOCK_SIZE),
            lblocks: Vec::with_capacity(lblock_len),
            indices: BitArray::with_capacity(sblock_len * code_size as u64),
            pointers: Vec::with_capacity(lblock_len),
            select1_unit_pointers: Vec::with_capacity(predicted_one_units),
            select0_unit_pointers: Vec::with_capacity(predicted_zero_units),
            last_sblock_bits: 0,
            pointer: 0,
        }
    }

    /// Estimate average code size.
    fn get_avg_code_size(true_odds: f64) -> u32 {
        let pivot = SBLOCK_WIDTH as f64 * true_odds;
        let pivot_size = TABLE.get_code_size(pivot as u32) as u32;
        let rounding = 4;
        let upper_size = (pivot_size + rounding - 1) / rounding * rounding;
        return upper_size.clamp(0, SBLOCK_WIDTH as u32);
    }

    #[roxygen]
    /// Constructs a new, empty [`BitVector`] with at least the specified capacity.
    pub fn with_odds(
        /// Amount of bits to store.
        capacity: u64,
        /// Probability between `0.0` and `1.0` for which `true` bits occur,
        /// and is used to predict the storage required.
        ///
        /// Probabilities around `0.5` represent the highest entropy and
        /// allocate the maximum required since it is unlikely to compress.
        odds: f64,
    ) -> Self {
        let true_odds = odds.clamp(0.0, 1.0);
        let false_odds = 1.0 - true_odds;
        let code_size = Self::get_avg_code_size(true_odds);
        Self::with_odds_and_code_size(capacity, true_odds, false_odds, code_size)
    }

    /// Constructs a new, empty [`BitVector`] with at least the specified capacity.
    ///
    /// Equivalent to [`with_odds`] with odds `0.5` (highest entropy).
    ///
    /// [`with_odds`]: BitVector::with_odds
    pub fn with_capacity(capacity: u64) -> Self {
        Self::with_odds_and_code_size(capacity, 0.5, 0.5, SBLOCK_WIDTH as u32)
    }

    /// Appends a bit at the end of the vector.
    pub fn push(&mut self, b: bool) {
        if b {
            self.last_sblock_bits |= 1 << (self.len % SBLOCK_WIDTH);
            self.ones += 1;
            if self.ones % SELECT_UNIT_NUM == 0 {
                self.push_select_unit(true);
            }
        } else {
            let zeros = self.len - self.ones + 1;
            if zeros % SELECT_UNIT_NUM == 0 {
                self.push_select_unit(false);
            }
        }
        self.len += 1;

        if self.len % SBLOCK_WIDTH == 0 {
            self.push_blocks();
        }
    }

    #[cold]
    fn push_select_unit(&mut self, b: bool) {
        let vec = if b {
            &mut self.select1_unit_pointers
        } else {
            &mut self.select0_unit_pointers
        };
        vec.push((self.len >> LBLOCK_SIZE) as usize)
    }

    #[cold]
    fn push_blocks(&mut self) {
        let last_sblock = self.last_sblock_bits.count_ones();
        let last_sblock_pos = self.len / SBLOCK_WIDTH - 1;
        self.sblocks
            .set_word(last_sblock_pos, SBLOCK_SIZE, last_sblock as u64);

        let (index, index_size) = TABLE.encode(self.last_sblock_bits, last_sblock);
        self.indices.set_slice(self.pointer, index_size, index);
        self.pointer += index_size;
        self.last_sblock_bits = 0;

        if self.len % LBLOCK_WIDTH == 0 {
            self.lblocks.push(self.ones);
            self.pointers.push(self.pointer);
        }
    }

    pub fn shrink_to_fit(&mut self) {
        self.sblocks.shrink_to_fit();
        self.lblocks.shrink_to_fit();
        self.indices.shrink_to_fit();
        self.pointers.shrink_to_fit();
        self.select1_unit_pointers.shrink_to_fit();
        self.select0_unit_pointers.shrink_to_fit();
    }

    fn get_unit(&self, b: bool, r: u64) -> usize {
        let vec = if b {
            &self.select1_unit_pointers
        } else {
            &self.select0_unit_pointers
        };
        let index = (r / SELECT_UNIT_NUM) as usize;
        *vec.get(index.wrapping_sub(1)).unwrap_or(&0)
    }

    fn get_lblock(&self, pos: usize) -> u64 {
        *self.lblocks.get(pos.wrapping_sub(1)).unwrap_or(&0)
    }

    fn get_pointer(&self, pos: usize) -> u64 {
        *self.pointers.get(pos.wrapping_sub(1)).unwrap_or(&0)
    }
    
    #[inline(never)]
    fn get_pointer_and_rank(&self, table: &ComboTable, i: u64) -> (u64, u64) {
        let lblock_pos = i / LBLOCK_WIDTH;
        let sblock_start_pos = lblock_pos * (LBLOCK_WIDTH / SBLOCK_WIDTH);
        let sblock_end_pos = i / SBLOCK_WIDTH;
        let mut pointer = self.get_pointer(lblock_pos as usize);
        let mut rank = self.get_lblock(lblock_pos as usize);

        for j in sblock_start_pos..sblock_end_pos {
            let k = self.sblocks.get_word(j, SBLOCK_SIZE);
            pointer += table.get_code_size(k as u32);
            rank += black_box(k); // prevent eager autovectorization
        }
        (pointer, rank)
    }

    /// Decode bits up to end of slice (`sblock[0..(i % SBLOCK_WIDTH + size)]`).
    /// Returns whole block when not packed.
    fn decode_sblock(&self, i: u64, size: NonZeroU32) -> u64 {
        let sblock_end_pos = i / SBLOCK_WIDTH;
        let sblock = self.sblocks.get_word(sblock_end_pos, SBLOCK_SIZE) as u32;
        if sblock == 0 {
            return 0;
        }

        let table = TABLE.as_ref();
        let pointer = self.get_pointer_and_rank(table, i).0;
        let code_size = table.get_code_size(sblock);
        let index = self.indices.get_slice(pointer, code_size);
        if code_size == SBLOCK_WIDTH {
            return index;
        }

        let end = size.saturating_add((i % SBLOCK_WIDTH) as u32);
        table.decode_index(index, sblock, end.get().into())
    }

    fn find_lblock_pos(&self, b: bool, r: u64) -> usize {
        let mut lblock_pos = self.get_unit(b, r);
        while lblock_pos < self.lblocks.len() {
            let lblock = self.lblocks[lblock_pos];
            let rank = phi_sub(b, LBLOCK_WIDTH * (lblock_pos as u64 + 1), lblock);
            if rank >= r {
                break;
            }
            lblock_pos += 1;
        }
        lblock_pos
    }
}

static TRUE: bool = true;
static FALSE: bool = false;

impl Index<u64> for BitVector {
    type Output = bool;

    fn index(&self, index: u64) -> &Self::Output {
        if self.get(index) {
            &TRUE
        } else {
            &FALSE
        }
    }
}

impl FID for BitVector {
    fn len(&self) -> u64 {
        self.len
    }

    fn get(&self, i: u64) -> bool {
        debug_assert!(i < self.len);

        let excess = self.len - i;
        let last_sblock_width = self.len % SBLOCK_WIDTH;
        let sblock = if excess <= last_sblock_width {
            self.last_sblock_bits
        } else {
            self.decode_sblock(i, NonZeroU32::new(1).unwrap())
        };
        sblock.wrapping_shr(i as u32) & 1 != 0
    }

    fn get_slice(&self, i: u64, size: u64) -> u64 {
        debug_assert!(size <= 64);

        let slice_end = i + size;
        assert!(slice_end <= self.len);

        let sblock_end_pos = i / SBLOCK_WIDTH;
        let hi_start = (sblock_end_pos + 1) * SBLOCK_WIDTH;
        let hi_size = slice_end.saturating_sub(hi_start);
        let lo_size = size - hi_size;

        let last_sblock_width = self.len % SBLOCK_WIDTH;
        let packed_len = self.len - last_sblock_width;

        let lo_block = if (i < packed_len) && (lo_size != 0) {
            self.decode_sblock(i, NonZeroU32::new(lo_size as u32).unwrap())
        } else {
            self.last_sblock_bits
        };

        let hi_block = if (hi_start < packed_len) && (hi_size != 0) {
            self.decode_sblock(hi_start, NonZeroU32::new(hi_size as u32).unwrap())
        } else {
            self.last_sblock_bits
        };

        let lo_bits = lo_block.wrapping_shr(i as u32) & mask_u64(lo_size);
        let hi_bits = (hi_block & mask_u64(hi_size)).wrapping_shl(lo_size as u32);
        return hi_bits | lo_bits;
    }

    fn get_word(&self, i: u64, size: u64) -> u64 {
        let i = i * size;
        if size == SBLOCK_WIDTH {
            let slice_end = i + size;
            assert!(slice_end <= self.len);

            return self.decode_sblock(i, NonZeroU32::new(size as u32).unwrap());
        }
        self.get_slice(i, size)
    }

    fn rank1(&self, i: u64) -> u64 {
        if self.len <= i {
            return self.ones;
        }
        let excess = self.len - i;
        let last_sblock_width = self.len % SBLOCK_WIDTH;
        if excess <= last_sblock_width {
            let last_ones = (self.last_sblock_bits >> (last_sblock_width - excess)).count_ones();
            return self.ones - last_ones as u64;
        }

        let table = TABLE.as_ref();
        let sblock_end_pos = i / SBLOCK_WIDTH;
        let (pointer, rank) = self.get_pointer_and_rank(table, i);

        let sblock = self.sblocks.get_word(sblock_end_pos, SBLOCK_SIZE) as u32;
        let code_size = table.get_code_size(sblock);
        let index = self.indices.get_slice(pointer, code_size);

        rank + table.decode_rank1(index, sblock, (i - sblock_end_pos * SBLOCK_WIDTH) as u32) as u64
    }

    fn select(&self, b: bool, r: u64) -> u64 {
        if b {
            self.select1(r)
        } else {
            self.select0(r)
        }
    }

    fn select0(&self, r: u64) -> u64 {
        self.select::<false>(r)
    }

    fn select1(&self, r: u64) -> u64 {
        self.select::<true>(r)
    }
}

impl BitVector {
    #[allow(non_upper_case_globals)]
    fn select<const b: bool>(&self, r: u64) -> u64 {
        let phi_len = phi_sub(b, self.len, self.ones);
        if phi_len <= r {
            return self.len;
        }

        let last_sblk_bits = self.last_sblock_bits;
        let last_sblk_width = self.len % SBLOCK_WIDTH;
        let last_sblk = phi_sub(b, last_sblk_width, last_sblk_bits.count_ones() as u64);
        if phi_len - r <= last_sblk {
            let k = self.len - last_sblk_width;
            let rank = r - (phi_len - last_sblk);
            let bits = if b { !last_sblk_bits } else { last_sblk_bits };
            let select = ComboTable::select0_raw(bits, rank as u32);
            return k + select as u64;
        }

        let table = TABLE.as_ref();
        let lblock_pos = self.find_lblock_pos(b, r);
        let lblock = self.get_lblock(lblock_pos);

        let mut sblock_pos = lblock_pos as u64 * (LBLOCK_WIDTH / SBLOCK_WIDTH);
        let mut sblock;
        let mut rank = phi_sub(b, LBLOCK_WIDTH * (lblock_pos as u64), lblock);
        let mut pointer = self.get_pointer(lblock_pos);
        loop {
            sblock = self.sblocks.get_word(sblock_pos, SBLOCK_SIZE) as u32;
            let next_rank = rank + phi_sub(b, SBLOCK_WIDTH, sblock as u64);
            if next_rank > r {
                break;
            }
            rank = next_rank;
            pointer += table.get_code_size(sblock);
            sblock_pos += 1;
        }

        let code_size = table.get_code_size(sblock);
        let index = self.indices.get_slice(pointer, code_size);
        let select_r = (r - rank) as u32;
        let select_sblock = if b {
            table.decode_select1(index, sblock, select_r)
        } else {
            table.decode_select0(index, sblock, select_r)
        } as u64;
        sblock_pos * SBLOCK_WIDTH + select_sblock
    }
}

impl<'i> IntoIterator for &'i BitVector {
    type Item = bool;

    type IntoIter = FidBitIter<'i, BitVector>;

    fn into_iter(self) -> Self::IntoIter {
        FidBitIter::new(self)
    }
}

impl From<&[bool]> for BitVector {
    fn from(value: &[bool]) -> Self {
        let mut vec = Self::with_capacity(value.len() as u64);
        for b in value {
            vec.push(*b);
        }
        vec
    }
}

impl FromIterator<bool> for BitVector {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut vec = Self::with_capacity(iter.size_hint().0 as u64);
        for b in iter {
            vec.push(b);
        }
        vec
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bit_arr;
    use rand::{Rng, SeedableRng, StdRng};

    const TEST_PROB: &[f64] = &[0.0, 0.01, 0.5, 0.99, 1.0];
    const TEST_SIZE: &[u64] = &[
        1,
        SBLOCK_WIDTH / 2,
        SBLOCK_WIDTH,
        LBLOCK_WIDTH - SBLOCK_WIDTH,
        LBLOCK_WIDTH - SBLOCK_WIDTH / 2,
        LBLOCK_WIDTH,
        SELECT_UNIT_NUM - LBLOCK_WIDTH,
        SELECT_UNIT_NUM,
        SELECT_UNIT_NUM + LBLOCK_WIDTH,
        SELECT_UNIT_NUM + LBLOCK_WIDTH + SBLOCK_WIDTH / 2,
        SELECT_UNIT_NUM + LBLOCK_WIDTH + SBLOCK_WIDTH,
        SELECT_UNIT_NUM * 2,
        SELECT_UNIT_NUM * 10 + LBLOCK_WIDTH + SBLOCK_WIDTH + SBLOCK_WIDTH / 2,
    ];

    #[test]
    fn test_construct() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::with_odds(n, p);
                for _ in 0..n {
                    let b = rng.gen_bool(p);
                    bv.push(b);
                }
            }
        }
    }

    #[test]
    fn test_rank1() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut ba = bit_arr![false; n];
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    ba.set_bit(i, b);
                    bv.push(b);
                }

                let mut rank = 0;
                for i in 0..n {
                    assert_eq!(rank, bv.rank1(i));
                    rank += ba.get_bit(i) as u64;
                }
            }
        }
    }

    #[test]
    fn test_select1() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut select_ans = vec![];
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    bv.push(b);
                    if b {
                        select_ans.push(i);
                    }
                }

                for (i, &r) in select_ans.iter().enumerate() {
                    assert_eq!(bv.select1(i as u64), r);
                }
            }
        }
    }

    #[test]
    fn test_select0() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut select_ans = vec![];
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    bv.push(b);
                    if !b {
                        select_ans.push(i);
                    }
                }

                for (i, &r) in select_ans.iter().enumerate() {
                    assert_eq!(bv.select0(i as u64), r);
                }
            }
        }
    }

    fn gen_rng<F>(f: F)
    where
        F: Fn(u64, BitVector, BitArray),
    {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut ba = bit_arr![false; n];
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    ba.set_bit(i, b);
                    bv.push(b);
                }

                f(n, bv, ba);
            }
        }
    }

    #[test]
    fn get() {
        gen_rng(|n, bv, ba| {
            for i in 0..n {
                assert_eq!(bv.get(i), ba.get_bit(i));
            }
        });
    }

    #[test]
    #[should_panic]
    fn get_empty_slice_out_of_bounds() {
        let bv = BitVector::new();
        bv.get_slice(129, 0);
    }

    #[test]
    fn get_empty_slice() {
        gen_rng(|n, bv, _| {
            for i in 0..n {
                assert_eq!(bv.get_slice(i, 0), 0);
            }
        });
    }

    #[test]
    fn get_word() {
        gen_rng(|n, bv, ba| {
            for word_size in &[7, SBLOCK_WIDTH] {
                for i in 0..(n / word_size) {
                    assert_eq!(bv.get_word(i, *word_size), ba.get_word(i, *word_size));
                }
            }
        });
    }

    #[cfg(feature = "serde")]
    #[cfg_attr(not(feature = "serde"), ignore)]
    #[test]
    fn test_serialize_rank1() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut ba = bit_arr![false; n];
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    ba.set_bit(i, b);
                    bv.push(b);
                }

                let encoded = bincode::serialize(&bv).unwrap();
                let bv: BitVector = bincode::deserialize(&encoded).unwrap();

                let mut rank = 0;
                for i in 0..n {
                    assert_eq!(rank, bv.rank1(i));
                    rank += ba.get_bit(i) as u64;
                }
            }
        }
    }
}
