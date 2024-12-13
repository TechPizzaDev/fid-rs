#[inline(always)]
pub const fn mask_u64(size: u64) -> u64 {
    let mask = if size == 0 { 0 } else { !0u64 };
    mask.wrapping_shr(u64::BITS - size as u32)
}
