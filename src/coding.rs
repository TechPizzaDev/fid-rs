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

pub fn decode_raw(mut index: u64, mut sblock: usize, end: usize) -> u64 {
    debug_assert!(sblock <= SBLOCK_WIDTH as usize);
    debug_assert!(end <= SBLOCK_WIDTH as usize);

    let mut bits = 0;
    let mut i = 0;
    while (i < end) && (sblock > 0) {
        // SAFETY: `sblock` and `end` asserts
        let base = unsafe { get_combination_size_unchecked(i as u64, sblock) };
        if index >= base {
            index -= base;
            bits |= 1 << i;
            sblock -= 1;
        }
        i += 1;
    }
    bits
}

pub fn decode_bit(mut index: u64, k: usize, p: usize) -> bool {
    debug_assert!(k <= SBLOCK_WIDTH as usize);
    debug_assert!(p <= SBLOCK_WIDTH as usize);

    // SAFETY: `k` and `p` asserts
    unsafe {
        let mut l = 0;
        for i in 0..p {
            let base = get_combination_size_unchecked(i as u64, k - l);
            if index >= base {
                index -= base;
                l += 1;
                if l == k {
                    break;
                }
            }
        }
        index >= get_combination_size_unchecked(p as u64, k - l)
    }
}

pub fn select1_raw(mut bits: u64, mut r: usize) -> u64 {
    let mut i = 0;
    while bits > 0 {
        if bits & 1 == 1 {
            if r == 0 {
                return i;
            }
            r -= 1;
        }
        i += 1;
        bits >>= 1;
    }
    64
}

pub fn select0_raw(bits: u64, mut r: u32) -> u64 {
    let mut i = 0;
    while i < 64 {
        let bits = bits >> i;
        let zeros = bits.trailing_zeros();
        let count = if zeros != 0 {
            if zeros > r {
                return (i + r) as u64;
            }
            r -= zeros;
            zeros
        } else {
            bits.trailing_ones()
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

pub fn decode_select1(mut index: u64, k: usize, r: usize) -> u64 {
    assert!(k <= SBLOCK_WIDTH as usize);

    let code_size = CODE_SIZE[k] as u64;
    if code_size == SBLOCK_WIDTH {
        return select1_raw(index, r);
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH {
        // SAFETY: `k` assert
        let base = unsafe { get_combination_size_unchecked(i, k - l) };

        if index >= base {
            if l == r {
                return i;
            }
            index -= base;
            l += 1;
        }
    }
    64
}

pub fn decode_select0(mut index: u64, k: usize, r: usize) -> u64 {
    assert!(k <= SBLOCK_WIDTH as usize);

    let code_size = CODE_SIZE[k] as u64;
    if code_size == SBLOCK_WIDTH {
        return select0_raw(index, r as u32);
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH {
        // SAFETY: `k` assert
        let base = unsafe { get_combination_size_unchecked(i, k - l) };

        if index >= base {
            index -= base;
            l += 1;
        } else if i as usize - l == r {
            return i;
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
        let code_size = CODE_SIZE[sblock] as u64;
        if code_size == SBLOCK_WIDTH {
            return index;
        }
        decode_raw(index, sblock, SBLOCK_WIDTH as usize)
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
        assert_eq!(decode_select1(encode(u64::MAX, 64).0, 64, 64), 64);

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            let mut ans = 0;
            for r in 0..k {
                ans += (bits >> ans).trailing_zeros();
                assert_eq!(decode_select1(encode(bits, k).0, k, r), ans as u64);
                ans += 1;
            }
        }
    }

    #[test]
    fn test_decode_select0() {
        assert_eq!(decode_select0(encode(!0u64 >> 32, 32).0, 32, 64), 64);

        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            let mut ans = 0;
            for r in 0..(64 - k) {
                ans += (bits >> ans).trailing_ones();
                assert_eq!(decode_select0(encode(bits, k).0, k, r), ans as u64);
                ans += 1;
            }
        }
    }

    #[test]
    fn test_decode_bit() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as usize;
            for p in 0..64 {
                let ans = (bits >> p) & 1 == 1;
                let (encoded, code_size) = encode(bits, k);
                let decoded = if code_size == SBLOCK_WIDTH {
                    (encoded >> p) & 1 == 1
                } else {
                    decode_bit(encoded, k, p)
                };
                assert_eq!(
                    decoded, ans,
                    "the {}-th bit of {:064b} is {}",
                    p, bits, ans as u8,
                );
            }
        }
    }
}
