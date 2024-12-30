use roxygen::{arguments_section, roxygen};

use crate::tables::*;

#[inline(always)]
#[roxygen]
pub fn get_combination_size(
    /// Combination index.
    i: u32,
    /// Size index.
    k: u32,
) -> u64 {
    const W: u32 = SBLOCK_WIDTH as u32;
    debug_assert!(i < W && k <= W);

    let offset = (W - i - 1) * (W + 1);
    COMBINATION[(offset + k) as usize]
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
    mut k: u32,
) -> (u64, u64) {
    debug_assert!(bits.count_ones() == k);

    let code_size = CODE_SIZE[k as usize] as u64;
    if code_size == SBLOCK_WIDTH {
        return (bits, code_size);
    }

    let mut code = 0;
    for i in 0..SBLOCK_WIDTH as u32 {
        if (bits >> i) & 1 > 0 {
            code += get_combination_size(i, k);
            k -= 1;
        }
    }
    (code, code_size)
}

pub fn decode_index(mut index: u64, mut k: u32, p: u32) -> u64 {
    assert!(p <= SBLOCK_WIDTH as u32);

    let mut bits = 0;
    for i in 0..p {
        let base = get_combination_size(i, k);
        if index >= base {
            index -= base;
            bits |= 1 << i;
            k = k.wrapping_sub(1);
        }
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

pub fn decode_rank1(mut index: u64, k: u32, p: u32) -> u32 {
    assert!(p <= SBLOCK_WIDTH as u32);

    let code_size = CODE_SIZE[k as usize];
    if code_size as u64 == SBLOCK_WIDTH {
        return (index & ((1 << p) - 1)).count_ones();
    };

    let mut l = 0;
    for i in 0..p {
        let base = get_combination_size(i, k - l);
        if index >= base {
            index -= base;
            l += 1;
            if l == k {
                break;
            }
        }
    }
    l
}

pub fn decode_select1(mut index: u64, k: u32, r: u32) -> u32 {
    let code_size = CODE_SIZE[k as usize] as u64;
    if code_size == SBLOCK_WIDTH {
        return select0_raw(!index, r);
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH as u32 {
        let base = get_combination_size(i, k - l);
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

pub fn decode_select0(mut index: u64, k: u32, r: u32) -> u32 {
    let code_size = CODE_SIZE[k as usize] as u64;
    if code_size == SBLOCK_WIDTH {
        return select0_raw(index, r);
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH as u32 {
        let base = get_combination_size(i, k - l);
        if index >= base {
            index -= base;
            l += 1;
        } else if i - l == r {
            return i;
        }
    }
    64
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

        let code_size = CODE_SIZE[sblock as usize] as u64;
        if code_size == SBLOCK_WIDTH {
            return index;
        }

        decode_index(index, sblock, SBLOCK_WIDTH as u32)
    }

    #[test]
    fn test_encode_decode_rng() {
        let n = 1000;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones();
            assert_eq!(decode(encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_encode_decode_log() {
        for n in 0..=u64::BITS {
            let bits: u64 = mask_u64(n as u64);
            let k = bits.count_ones();
            assert_eq!(n, k);
            assert_eq!(decode(encode(bits, k).0, k), bits);
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
            let k = bits.count_ones();
            let mut ans = 0;
            for r in 0..k {
                ans += (bits >> ans).trailing_zeros();
                assert_eq!(decode_select1(encode(bits, k).0, k, r), ans);
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
            let k = bits.count_ones();
            let mut ans = 0;
            for r in 0..(64 - k) {
                ans += (bits >> ans).trailing_ones();
                assert_eq!(decode_select0(encode(bits, k).0, k, r), ans);
                ans += 1;
            }
        }
    }
}
