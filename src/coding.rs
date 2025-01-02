use std::sync::LazyLock;

use roxygen::{arguments_section, roxygen};

use crate::util::log2;

pub(crate) const SBLOCK_WIDTH: u64 = 64;
const ROWS: usize = SBLOCK_WIDTH as usize + 1;
const ROWS_PADDED: usize = ROWS.next_power_of_two();

/// TODO: describe threshold
const MAX_CODE_SIZE: u32 = 48;

type CodeSizes = [u8; ROWS_PADDED];
type CodeRow = [u64; SBLOCK_WIDTH as usize];
type CodeMatrix = [CodeRow; ROWS];

// Box is required to not bloat exe with zeros.
pub static TABLE: LazyLock<Box<ComboTable>> = LazyLock::new(|| {
    let mut slot: Box<_> = Default::default();
    generate_table(&mut slot);
    slot
});

pub struct ComboTable {
    sizes: CodeSizes,
    matrix: CodeMatrix,
}

impl Default for ComboTable {
    fn default() -> Self {
        Self {
            sizes: [0; ROWS_PADDED],
            matrix: [[0; SBLOCK_WIDTH as usize]; ROWS],
        }
    }
}

impl ComboTable {
    #[inline(always)]
    pub fn get_code_size(&self, i: u32) -> u64 {
        *self.sizes.get(i as usize).unwrap_or(&0) as u64
    }

    #[inline(always)]
    #[roxygen]
    fn get_combination_size(
        &self,
        /// Combination index.
        i: u32,
        /// Size index.
        k: u32,
    ) -> u64 {
        const W: u32 = SBLOCK_WIDTH as u32;
        debug_assert!(i < W && k <= W);

        self.matrix[k as usize][i as usize]
    }

    #[roxygen]
    /// Encode an integer using a table of combinations.
    #[arguments_section]
    /// # Panics
    /// `k` exceeds the count of ones in `bits`.
    pub fn encode(
        &self,
        /// Value to encode.
        bits: u64,
        /// Count of ones in `bits`.
        mut k: u32,
    ) -> (u64, u64) {
        debug_assert!(bits.count_ones() == k);

        let code_size = self.get_code_size(k);
        if code_size == SBLOCK_WIDTH {
            return (bits, code_size);
        }

        let mut code = 0;
        let mut i = 0;
        while (i < SBLOCK_WIDTH as u32) && (k <= SBLOCK_WIDTH as u32) {
            let head = bits >> i;
            if head & 1 > 0 {
                code += self.get_combination_size(i, k);
                k = k.wrapping_sub(1);
                i += 1;
            } else {
                i += head.trailing_zeros();
            }
        }
        (code, code_size)
    }

    pub fn decode_index(&self, mut index: u64, mut k: u32, p: u32) -> u64 {
        assert!(p <= SBLOCK_WIDTH as u32);

        let mut bits = 0;
        let mut i = 0;
        while (i < p) && (k <= SBLOCK_WIDTH as u32) {
            let base = self.get_combination_size(i, k);
            if index >= base {
                index -= base;
                bits |= 1 << i;
                k = k.wrapping_sub(1);
            }
            i += 1;
        }
        bits
    }

    #[inline(never)]
    pub fn select0_raw(bits: u64, mut r: u32) -> u32 {
        let mut i = 0;
        while i < 64 {
            let slice = bits >> i;
            let zeros = slice.trailing_zeros();
            let count = if zeros != 0 {
                if zeros > r {
                    return i + r;
                }
                r -= zeros;
                zeros
            } else {
                slice.trailing_ones()
            };
            i += count;
        }
        64
    }

    pub fn decode_rank1(&self, mut index: u64, k: u32, p: u32) -> u32 {
        assert!(p <= SBLOCK_WIDTH as u32);

        let code_size = self.get_code_size(k);
        if code_size == SBLOCK_WIDTH {
            return (index & ((1 << p) - 1)).count_ones();
        };

        let mut l = 0;
        let mut i = 0;
        while (i < p) && (k.wrapping_sub(l) <= SBLOCK_WIDTH as u32) {
            let base = self.get_combination_size(i, k - l);
            if index >= base {
                index -= base;
                l += 1;
                if l == k {
                    break;
                }
            }
            i += 1;
        }
        l
    }

    pub fn decode_select1(&self, mut index: u64, k: u32, r: u32) -> u32 {
        let code_size = self.get_code_size(k);
        if code_size == SBLOCK_WIDTH {
            return Self::select0_raw(!index, r);
        }

        let mut l = 0;
        let mut i = 0;
        while (i < SBLOCK_WIDTH as u32) && (k.wrapping_sub(l) <= SBLOCK_WIDTH as u32) {
            let base = self.get_combination_size(i, k - l);
            if index >= base {
                if l == r {
                    return i;
                }
                index -= base;
                l += 1;
            }
            i += 1;
        }
        64
    }

    pub fn decode_select0(&self, mut index: u64, k: u32, r: u32) -> u32 {
        let code_size = self.get_code_size(k);
        if code_size == SBLOCK_WIDTH {
            return Self::select0_raw(index, r);
        }

        let mut l = 0;
        let mut i = 0;
        while (i < SBLOCK_WIDTH as u32) && (k.wrapping_sub(l) <= SBLOCK_WIDTH as u32) {
            let base = self.get_combination_size(i, k - l);
            if index >= base {
                index -= base;
                l += 1;
            } else if i - l == r {
                return i;
            }
            i += 1;
        }
        64
    }
}

const fn generate_table(table: &mut ComboTable) {
    let matrix = &mut table.matrix;
    let sizes = &mut table.sizes;

    let mut i = 0;
    while i < SBLOCK_WIDTH as usize {
        matrix[0][i] = 1;
        i += 1;
    }

    let mut y = 1;
    while y < SBLOCK_WIDTH as usize {
        // Prefix sum of previous row excluding the last element, 
        // stored in reverse for optimal read-access.
        let mut x = SBLOCK_WIDTH as usize - 1 - 1;
        while x < SBLOCK_WIDTH as usize {
            matrix[y][x] = matrix[y - 1][x + 1] + matrix[y][x + 1];
            x = x.wrapping_sub(1);
        }

        // Calculating size after row is 2x faster than doing it in a separate function.
        let val = matrix[y - 1][0] + matrix[y][0];
        let size = log2(val - 1) + 1;
        sizes[y] = if size <= MAX_CODE_SIZE {
            size as u8
        } else {
            SBLOCK_WIDTH as u8
        };

        y += 1;
    }
}

#[cfg(test)]
mod tests {
    use crate::util::mask_u64;

    use super::*;
    use rand::{Rng, SeedableRng, StdRng};

    fn decode(index: u64, sblock: u32) -> u64 {
        if sblock == 0 {
            return 0;
        }

        let code_size = TABLE.get_code_size(sblock);
        if code_size == SBLOCK_WIDTH {
            return index;
        }

        TABLE.decode_index(index, sblock, SBLOCK_WIDTH as u32)
    }

    #[test]
    fn test_encode_decode_rng() {
        let n = 1000;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones();
            assert_eq!(decode(TABLE.encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_encode_decode_log() {
        for n in 0..=u64::BITS {
            let bits: u64 = mask_u64(n as u64);
            let k = bits.count_ones();
            assert_eq!(n, k);
            assert_eq!(decode(TABLE.encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_decode_rank1() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones();
            for p in 0..64 {
                let ans = (bits & ((1 << p) - 1)).count_ones();
                assert_eq!(TABLE.decode_rank1(TABLE.encode(bits, k).0, k, p), ans);
            }
        }
    }

    #[test]
    fn test_decode_select1() {
        assert_eq!(
            TABLE.decode_select1(TABLE.encode(u64::MAX, 64).0, 64, 64),
            64
        );

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones();
            let mut ans = 0;
            for r in 0..k {
                ans += (bits >> ans).trailing_zeros();
                assert_eq!(TABLE.decode_select1(TABLE.encode(bits, k).0, k, r), ans);
                ans += 1;
            }
        }
    }

    #[test]
    fn test_decode_select0() {
        assert_eq!(
            TABLE.decode_select0(TABLE.encode(!0u64 >> 32, 32).0, 32, 64),
            64
        );

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones();
            let mut ans = 0;
            for r in 0..(64 - k) {
                ans += (bits >> ans).trailing_ones();
                assert_eq!(TABLE.decode_select0(TABLE.encode(bits, k).0, k, r), ans);
                ans += 1;
            }
        }
    }
}
