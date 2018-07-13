use bit_array::BitArray;
use fid::FID;
use std::fmt;

const SBLOCK_WIDTH: u64 = 64;
const SBLOCK_SIZE: u64 = 7; // ceil(log(SBLOCK_SIZE + 1))
const LBLOCK_WIDTH: u64 = 1024;
const SELECT_UNIT_NUM: u64 = 4096;

/// Include two constant arrays generated by `build.rs`.
/// ```
/// const COMBINATION: [[u64; SBLOCK_WIDTH + 1]; SBLOCK_WIDTH + 1];
/// const CODE_SIZE: [usize; SBLOCK_WIDTH + 1];
/// ```
include!(concat!(env!("OUT_DIR"), "/const.rs"));

/// A succinct bit vector that supports FID operations (rank and select) in constant time.
///
/// Bits are divided in small and large blocks. Each small block is identified by
/// a class (number of 1s in the block) and an index within the class. Classes are
/// stored in ceil(log(SBLOCK_WIDTH + 1)) bits. Indices are stored in log(C(SBLOCK_WIDTH, index)) bits with enumerative code
/// if its compressed size is less than MAX_CODE_SIZE. Otherwise the bit pattern of the small block is explicitly stored as an index
/// for the sake of efficiency. This idea originally comes from [2]. For each large block, we store the number of 1s up to its beginning and
/// a pointer for the index of the first small block.
///
/// # Examples
///
/// ```
/// use fid::{BitVector, FID};
/// let mut bv = BitVector::new();
/// bv.push(false); bv.push(true); bv.push(true); bv.push(false);
/// bv.push(true); bv.push(true); bv.push(false); bv.push(true);
///
/// assert_eq!(bv.rank0(5), 2);
/// assert_eq!(bv.rank1(5), 3);
/// assert_eq!(bv.select0(2), 6);
/// assert_eq!(bv.select1(2), 4);
/// ```
///
/// # References
/// [1] Gonzalo Navarro and Eliana Providel. 2012. Fast, small, simple rank/select on bitmaps. In Proceedings of the 11th international conference on Experimental Algorithms (SEA'12), Ralf Klasing (Ed.). Springer-Verlag, Berlin, Heidelberg, 295-306. DOI=http://dx.doi.org/10.1007/978-3-642-30850-5_26
///
/// [2] rsdic by Daisuke Okanohara. [https://github.com/hillbig/rsdic](https://github.com/hillbig/rsdic)
pub struct BitVector {
    /// Length of the vector (number of bits)
    len: u64,
    /// Number of 1s
    ones: u64,
    /// Class identifiers (number of 1s) of small blocks of width `SBLOCK_WIDTH`,
    /// which are represented with `SBLOCK_SIZE` bits.
    sblocks: BitArray,
    /// Rank1 (number of 1s) up to the i-th super block.
    lblocks: Vec<u64>,
    /// Indices of each small block
    indices: BitArray,
    /// Pointers to `indices`
    pointers: Vec<u64>,

    select1_unit_pointers: Vec<usize>,
    select0_unit_pointers: Vec<usize>,

    last_sblock_bits: u64,
    pointer: u64,
}

impl BitVector {
    pub fn new() -> Self {
        BitVector {
            len: 0,
            ones: 0,
            sblocks: BitArray::new(0),
            lblocks: vec![0],
            indices: BitArray::new(0),
            pointers: vec![0],
            select1_unit_pointers: vec![0],
            select0_unit_pointers: vec![0],
            last_sblock_bits: 0,
            pointer: 0,
        }
    }

    /// Appends a bit at the end of the vector.
    pub fn push(&mut self, b: bool) {
        if b {
            self.last_sblock_bits |= 1 << (self.len % SBLOCK_WIDTH);
            self.ones += 1;
            if self.ones % SELECT_UNIT_NUM == 0 {
                self.select1_unit_pointers
                    .push((self.len / LBLOCK_WIDTH) as usize);
            }
        } else {
            let zeros = self.len - self.ones + 1;
            if zeros % SELECT_UNIT_NUM == 0 {
                self.select0_unit_pointers
                    .push((self.len / LBLOCK_WIDTH) as usize);
            }
        }
        self.len += 1;

        if self.len % SBLOCK_WIDTH == 0 {
            let last_sblock = self.last_sblock_bits.count_ones();
            let last_sblock_pos = self.len / SBLOCK_WIDTH - 1;
            self.sblocks.set_word(
                last_sblock_pos as usize,
                SBLOCK_SIZE as usize,
                last_sblock.into(),
            );

            let (index, index_size) = encode(self.last_sblock_bits, last_sblock as u8);
            self.indices
                .set_slice(self.pointer as usize, index_size as usize, index);
            self.pointer += index_size;

            self.last_sblock_bits = 0;

            if self.len % LBLOCK_WIDTH == 0 {
                self.lblocks.push(self.ones);
                self.pointers.push(self.pointer);
            }
        }
    }
}

impl fmt::Debug for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "len:    {}", self.len)?;
        writeln!(f, "ones:   {}", self.ones)?;
        write!(f, "sblock: ")?;
        for i in 0..(self.len / SBLOCK_WIDTH) {
            write!(
                f,
                "{} ",
                self.sblocks.get_word(i as usize, SBLOCK_SIZE as usize)
            )?;
        }
        writeln!(f, "{}", self.last_sblock_bits.count_ones())?;
        write!(f, "lblock: ")?;
        for lb in &self.lblocks {
            write!(f, "{} ", lb)?;
        }
        Ok(())
    }
}

impl FID for BitVector {
    fn len(&self) -> u64 {
        self.len
    }

    fn rank1(&self, i: u64) -> u64 {
        if self.len <= i {
            return self.ones;
        }
        let excess = self.len - i;
        let last_sblock_width = self.len % SBLOCK_WIDTH;
        if excess <= last_sblock_width {
            return self.ones
                - (self.last_sblock_bits >> (last_sblock_width - excess)).count_ones() as u64;
        }

        let lblock_pos = i / LBLOCK_WIDTH;
        let sblock_start_pos = lblock_pos * (LBLOCK_WIDTH / SBLOCK_WIDTH);
        let sblock_end_pos = i / SBLOCK_WIDTH;
        let mut pointer = self.pointers[lblock_pos as usize];
        let mut rank = self.lblocks[lblock_pos as usize];

        for j in sblock_start_pos..sblock_end_pos {
            let k = self.sblocks.get_word(j as usize, SBLOCK_SIZE as usize);
            rank += k;
            pointer += CODE_SIZE[k as usize];
        }
        let sblock = self.sblocks
            .get_word(sblock_end_pos as usize, SBLOCK_SIZE as usize);
        let code_size = CODE_SIZE[sblock as usize];
        let index = self.indices.get_slice(pointer as usize, code_size as usize);
        rank + decode_rank1(
            index,
            sblock as u8,
            (i - sblock_end_pos * SBLOCK_WIDTH) as u8,
        )
    }

    fn select1(&self, r: u64) -> u64 {
        if self.ones <= r {
            return self.len;
        }

        let mut lblock_pos = self.select1_unit_pointers[(r / SELECT_UNIT_NUM) as usize];
        let lblock_len = self.lblocks.len();
        while lblock_pos + 1 < lblock_len {
            let lblock = self.lblocks[lblock_pos + 1];
            if lblock >= r {
                break;
            }
            lblock_pos += 1;
        }

        if self.ones - r <= self.last_sblock_bits.count_ones().into() {
            let k = self.len - self.len % SBLOCK_WIDTH;
            let last_sblock = self.last_sblock_bits.count_ones() as u64;
            let rank = r - (self.ones - last_sblock);
            let select = select1_raw(self.last_sblock_bits, rank);
            return k + select;
        }

        let mut sblock_pos = lblock_pos * (LBLOCK_WIDTH / SBLOCK_WIDTH) as usize;
        let mut sblock = self.sblocks.get_word(sblock_pos, SBLOCK_SIZE as usize);
        let mut rank = self.lblocks[lblock_pos];
        let mut pointer = self.pointers[lblock_pos];
        while rank + sblock <= r {
            rank = rank + sblock;
            pointer += CODE_SIZE[sblock as usize];
            sblock_pos += 1;
            sblock = self.sblocks.get_word(sblock_pos, SBLOCK_SIZE as usize);
        }

        let code_size = CODE_SIZE[sblock as usize];
        let index = self.indices.get_slice(pointer as usize, code_size as usize);
        let select_sblock = decode_select1(index, sblock as u8, (r - rank) as u8);

        sblock_pos as u64 * SBLOCK_WIDTH + select_sblock
    }

    fn select0(&self, r: u64) -> u64 {
        let zeros = self.len - self.ones;
        if zeros <= r {
            return self.len;
        }

        let mut lblock_pos = self.select0_unit_pointers[(r / SELECT_UNIT_NUM) as usize];
        let lblock_len = self.lblocks.len();
        while lblock_pos + 1 < lblock_len {
            let lblock = LBLOCK_WIDTH * (lblock_pos as u64 + 1) - self.lblocks[lblock_pos + 1];
            if lblock >= r {
                break;
            }
            lblock_pos += 1;
        }

        let last_sblock_width = self.len % SBLOCK_WIDTH;
        if zeros - r <= last_sblock_width - (self.last_sblock_bits.count_ones() as u64) {
            let last_sblock = last_sblock_width - self.last_sblock_bits.count_ones() as u64;
            let rank = r - (zeros - last_sblock);
            let k = self.len - last_sblock_width;
            let select = select0_raw(self.last_sblock_bits, rank);
            return k + select;
        }

        let mut sblock_pos = lblock_pos * (LBLOCK_WIDTH / SBLOCK_WIDTH) as usize;
        let mut sblock = self.sblocks.get_word(sblock_pos, SBLOCK_SIZE as usize);
        let mut rank = LBLOCK_WIDTH * (lblock_pos as u64) - self.lblocks[lblock_pos];
        let mut pointer = self.pointers[lblock_pos];
        loop {
            let sblock_zero = SBLOCK_WIDTH - sblock;
            if rank + sblock_zero > r {
                break;
            }
            rank = rank + sblock_zero;
            pointer += CODE_SIZE[sblock as usize];
            sblock_pos += 1;
            sblock = self.sblocks.get_word(sblock_pos, SBLOCK_SIZE as usize);
        }

        let code_size = CODE_SIZE[sblock as usize];
        let index = self.indices.get_slice(pointer as usize, code_size as usize);
        let select_sblock = decode_select0(index, sblock as u8, (r - rank) as u8);

        sblock_pos as u64 * SBLOCK_WIDTH + select_sblock
    }
}

fn select1_raw(mut bits: u64, mut r: u64) -> u64 {
    let mut i = 0;
    while bits > 0 {
        if bits & 1 == 1 {
            if r == 0 {
                return i;
            }
            r -= 1;
        }
        i += 1;
        bits = bits >> 1;
    }
    64
}

fn select0_raw(mut bits: u64, mut r: u64) -> u64 {
    let mut i = 0;
    while i < 64 {
        if bits & 1 == 0 {
            if r == 0 {
                return i;
            }
            r -= 1;
        }
        i += 1;
        bits = bits >> 1;
    }
    64
}

fn encode(bits: u64, k: u8) -> (u64, u64) {
    let code_size = CODE_SIZE[k as usize];
    if code_size == SBLOCK_WIDTH {
        return (bits, code_size);
    }
    let mut l = 0;
    let mut code = 0;
    for i in 0..SBLOCK_WIDTH {
        if (bits >> i) & 1 > 0 {
            code += COMBINATION[(SBLOCK_WIDTH - i - 1) as usize][(k - l) as usize];
            l = l + 1;
            if l == k {
                break;
            }
        }
    }
    return (code, code_size);
}

#[allow(dead_code)]
fn decode(mut index: u64, k: u8) -> u64 {
    let code_size = CODE_SIZE[k as usize];
    if code_size == SBLOCK_WIDTH {
        return index;
    }

    let mut l = 0;
    let mut bits = 0;
    for i in 0..SBLOCK_WIDTH {
        let base = COMBINATION[(SBLOCK_WIDTH - i - 1) as usize][(k - l) as usize];
        if index >= base {
            bits |= 1 << i;
            index -= base;
            l = l + 1;
            if l == k {
                break;
            }
        }
    }
    bits
}

fn decode_rank1(mut index: u64, k: u8, p: u8) -> u64 {
    let code_size = CODE_SIZE[k as usize];
    if code_size == SBLOCK_WIDTH {
        return (index & ((1 << p) - 1)).count_ones() as u64;
    }

    let mut l = 0;
    for i in 0..(p as u64) {
        let base = COMBINATION[(SBLOCK_WIDTH - i - 1) as usize][(k - l) as usize];
        if index >= base {
            index -= base;
            l = l + 1;
            if l == k {
                break;
            }
        }
    }
    l as u64
}

fn decode_select1(mut index: u64, k: u8, r: u8) -> u64 {
    let code_size = CODE_SIZE[k as usize];
    if code_size == SBLOCK_WIDTH {
        return select1_raw(index, r.into());
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH {
        let base = COMBINATION[(SBLOCK_WIDTH - i - 1) as usize][(k - l) as usize];

        if index >= base {
            if l == r {
                return i;
            }
            index -= base;
            l = l + 1;
        }
    }
    return 64;
}

fn decode_select0(mut index: u64, k: u8, r: u8) -> u64 {
    let code_size = CODE_SIZE[k as usize];
    if code_size == SBLOCK_WIDTH {
        return select0_raw(index, r.into());
    }

    let mut l = 0;
    for i in 0..SBLOCK_WIDTH {
        let base = COMBINATION[(SBLOCK_WIDTH - i - 1) as usize][(k - l) as usize];

        if index >= base {
            index -= base;
            l = l + 1;
        } else {
            if i - (l as u64) == r as u64 {
                return i;
            }
        }
    }
    return 64;
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use self::rand::{Rng, SeedableRng, StdRng};
    use super::*;

    #[test]
    fn test_encode_decode() {
        let n = 1000;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as u8;
            assert_eq!(decode(encode(bits, k).0, k), bits);
        }
    }

    #[test]
    fn test_decode_rank1() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as u8;
            for p in 0..64 {
                let ans = (bits & ((1 << p) - 1)).count_ones() as u64;
                assert_eq!(decode_rank1(encode(bits, k).0, k, p), ans);
            }
        }
    }

    #[test]
    fn test_decode_select1() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as u8;
            let mut ans = 0;
            for r in 0..k {
                while ans < 64 {
                    if bits & (1 << ans) > 0 {
                        break;
                    }
                    ans += 1;
                }
                assert_eq!(decode_select1(encode(bits, k).0, k, r), ans);
                ans += 1;
            }
        }
    }

    #[test]
    fn test_decode_select0() {
        let n = 100;
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        for _ in 0..n {
            let bits: u64 = rng.gen();
            let k = bits.count_ones() as u8;
            let mut ans = 0;
            for r in 0..(64 - k) {
                while ans < 64 {
                    if bits & (1 << ans) == 0 {
                        break;
                    }
                    ans += 1;
                }
                assert_eq!(decode_select0(encode(bits, k).0, k, r), ans);
                ans += 1;
            }
        }
    }

    const TEST_PROB: &[f64] = &[0.01, 0.5, 0.99];
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
    fn test_rank1() {
        for &p in TEST_PROB {
            for &n in TEST_SIZE {
                let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
                let mut bv = BitVector::new();
                let mut ba = BitArray::new(n as usize);
                for i in 0..n {
                    let b = rng.gen_bool(p);
                    ba.set_bit(i as usize, b);
                    bv.push(b);
                }

                let mut rank = 0;
                for i in 0..n {
                    assert_eq!(rank, bv.rank1(i));
                    rank += ba.get_bit(i as usize) as u64;
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

}
