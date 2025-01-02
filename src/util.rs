
#[inline(always)]
pub const fn mask_u64(size: u64) -> u64 {
    let mask = if size == 0 { 0 } else { !0u64 };
    mask.wrapping_shr(u64::BITS - size as u32)
}

/// Conditionally subtracts `r` from `w` if `b` is false.
#[inline(always)]
pub const fn phi_sub(b: bool, w: u64, r: u64) -> u64 {
    if b {
        r
    } else {
        w - r
    }
}

#[inline(always)]
pub const fn log2(x: u64) -> u32 {
    (u64::BITS - 1) - (x | 1).leading_zeros()
}