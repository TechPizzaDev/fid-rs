use std::num::NonZeroU32;

use roxygen::{arguments_section, roxygen};

use crate::tables::*;

#[inline(always)]
#[roxygen]
/// Access [`COMBINATION`] without bounds checking.  
/// Asserting conditions for skipping bound checks allows
/// loops to be unrolled further and without a panic branch per iteration.
pub unsafe fn get_combination_size_unchecked(
    /// Combination index.
    i: u64,
    /// Size index.
    s: usize,
) -> u64 {
    debug_assert!(i <= SBLOCK_WIDTH);
    debug_assert!(s <= SBLOCK_WIDTH as usize);

    let offset = (SBLOCK_WIDTH - i - 1) * (SBLOCK_WIDTH + 1);
    *COMBINATION.get_unchecked(offset as usize + s)
}

#[roxygen]
/// Encode an integer using a table of combinations.
#[arguments_section]
/// # Panics
/// `k` exceeds the count of ones in `bits`.
pub fn encode(
    /// Value to encode.
    bits: u64,
    /// Count of ones in `bits`.
    k: usize,
) -> (u64, u64) {
    debug_assert!(bits.count_ones() as usize == k);

    let code_size = CODE_SIZE[k] as u64;
    if code_size == SBLOCK_WIDTH {
        return (bits, code_size);
    }

    let mut l = 0;
    let mut code = 0;
    for i in 0..SBLOCK_WIDTH {
        if (bits >> i) & 1 > 0 {
            // SAFETY: `bits` assert ensures `l` will not exceed `k`
            code += unsafe { get_combination_size_unchecked(i, k - l) };
            l += 1;
        }
    }
    (code, code_size)
}

pub fn decode_index(mut index: u64, sblock: NonZeroU32, end: NonZeroU32) -> u64 {
    let mut sblock = sblock.get();
    let end = end.get();

    debug_assert!(sblock <= SBLOCK_WIDTH as u32);
    debug_assert!(end <= SBLOCK_WIDTH as u32);

    let mut bits = 0;
    let mut i = 0;
    while (i < end) && (sblock > 0) {
        // SAFETY: `sblock` and `end` asserts
        let base = unsafe { get_combination_size_unchecked(i as u64, sblock as usize) };
        if index >= base {
            index -= base;
            bits |= 1 << i;
            sblock -= 1;
        }
        i += 1;
    }
    bits
}

#[inline(never)]
pub fn select0_raw(bits: u64, mut r: u64) -> u64 {
    let mut i = 0;
    while i < 64 {
        let slice = bits >> i;
        let zeros = slice.trailing_zeros() as u64;
        let count = if zeros != 0 {
            if zeros > r {
                return i + r;
            }
            r -= zeros;
            zeros
        } else {
            slice.trailing_ones() as u64
        };
        i += count;
    }
    64
}

pub fn decode_rank1(mut index: u64, k: usize, p: u64) -> u64 {
    assert!(k <= SBLOCK_WIDTH as usize);
    assert!(p <= SBLOCK_WIDTH);

    let code_size = CODE_SIZE[k] as u64;
    if code_size == SBLOCK_WIDTH {
        return (index & ((1 << p) - 1)).count_ones() as u64;
    }

    let mut l = 0;
    for i in 0..p {
        // SAFETY: `k` and `p` asserts
        let base = unsafe { get_combination_size_unchecked(i, k - l) };

        if index >= base {
            index -= base;
            l += 1;
            if l == k {
                break;
            }
        }
    }
    l as u64
}

pub fn decode_select(b: bool, mut index: u64, k: usize, r: u64) -> u64 {
    assert!(k <= SBLOCK_WIDTH as usize);

    let code_size = CODE_SIZE[k] as u64;
    if code_size == SBLOCK_WIDTH {
        let bits = if b { !index } else { index };
        return select0_raw(bits, r);
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH {
        // SAFETY: `k` assert
        let base = unsafe { get_combination_size_unchecked(i, k - l as usize) };
        if b {
            if index >= base {
                if l == r {
                    return i;
                }
                index -= base;
                l += 1;
            }
        } else {
            if index >= base {
                index -= base;
                l += 1;
            } else if i - l == r {
                return i;
            }
        }
    }
    64
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use crate::util::mask_u64;

    use self::rand::{Rng, SeedableRng, StdRng};
    use super::*;

    fn decode(index: u64, sblock: usize) -> u64 {
        if sblock == 0 {
            return 0;
        }

        let code_size = CODE_SIZE[sblock] as u64;
        if code_size == SBLOCK_WIDTH {
            return index;
        }

        decode_index(
            index,
            NonZeroU32::new(sblock as u32).unwrap(),
            NonZeroU32::new(SBLOCK_WIDTH as u32).unwrap(),
        )
    }

    #[test]
    fn test_encode_decode_rng() {
        let n = 1000;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            assert_eq!(decode(encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_encode_decode_log() {
        for n in 0..=u64::BITS {
            let bits: u64 = mask_u64(n as u64);
            let k = bits.count_ones() as usize;
            assert_eq!(n as usize, k);
            assert_eq!(decode(encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_decode_rank1() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            for p in 0..64 {
                let ans = u64::from((bits & ((1 << p) - 1)).count_ones());
                assert_eq!(decode_rank1(encode(bits, k).0, k, p), ans);
            }
        }
    }

    #[test]
    fn test_decode_select1() {
        assert_eq!(decode_select(true, encode(u64::MAX, 64).0, 64, 64), 64);

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            let mut ans = 0;
            for r in 0..k {
                ans += (bits >> ans).trailing_zeros();
                assert_eq!(
                    decode_select(true, encode(bits, k).0, k, r as u64),
                    ans as u64
                );
                ans += 1;
            }
        }
    }

    #[test]
    fn test_decode_select0() {
        assert_eq!(decode_select(false, encode(!0u64 >> 32, 32).0, 32, 64), 64);

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            let mut ans = 0;
            for r in 0..(64 - k) {
                ans += (bits >> ans).trailing_ones();
                assert_eq!(
                    decode_select(false, encode(bits, k).0, k, r as u64),
                    ans as u64
                );
                ans += 1;
            }
        }
    }
}
