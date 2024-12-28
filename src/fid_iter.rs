use crate::FID;
use std::iter::FusedIterator;

const BLOCK_SIZE: u64 = 64;

#[derive(Debug, Clone)]
pub struct FidBitIter<'i, T: FID> {
    fid: &'i T,
    len: u64,
    i: u64,
    bits: u64,
}

impl<'i, T: FID> FidBitIter<'i, T> {
    pub fn new(fid: &'i T) -> Self {
        Self {
            fid,
            len: fid.len(),
            i: 0,
            bits: 0,
        }
    }

    #[cold]
    fn refill(&mut self) -> bool {
        if self.len >= BLOCK_SIZE {
            self.bits = self.fid.get_word(self.i / BLOCK_SIZE, BLOCK_SIZE);
            self.len -= BLOCK_SIZE;
        } else if self.len > 0 {
            self.refill_tail();
        } else {
            return false;
        };
        return true;
    }

    fn refill_tail(&mut self) {
        let offset = BLOCK_SIZE - self.len;
        self.bits = self.fid.get_slice(self.i, self.len) << offset;

        // Adjust `i` to refill early since we're at the end.
        self.i = (self.i / BLOCK_SIZE) * BLOCK_SIZE + offset;
        self.len = 0;
    }

    #[inline(always)]
    fn next_bit(&mut self) -> Option<bool> {
        let bit = self.bits & (1 << (self.i % BLOCK_SIZE));
        self.i += 1;
        Some(bit != 0)
    }
}

impl<'i, T: FID> Iterator for FidBitIter<'i, T> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i % BLOCK_SIZE == 0 && !self.refill() {
            return None;
        }
        self.next_bit()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let prev = self.i;
        let size = self.len.min(n as u64); // prevent overflows
        self.i += size;
        self.len -= size;

        // Refill if block boundary was crossed *or* first block is not loaded.
        if (self.i / BLOCK_SIZE > prev / BLOCK_SIZE) || (prev % BLOCK_SIZE == 0) {
            if !self.refill() {
                return None;
            }
        }
        self.next_bit()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.len.try_into().unwrap_or(usize::MAX);
        (size, Some(size))
    }
}

impl<'i, T: FID> ExactSizeIterator for FidBitIter<'i, T> {}

impl<'i, T: FID> FusedIterator for FidBitIter<'i, T> {}

#[cfg(test)]
mod tests {
    use rand::{Rng, SeedableRng, StdRng};
    use crate::BitVector;

    use super::BLOCK_SIZE;

    const TEST_SIZE: &[u64] = &[
        0,
        1,
        BLOCK_SIZE - 1,
        BLOCK_SIZE,
        BLOCK_SIZE * 2 - 1,
        BLOCK_SIZE * 2,
    ];

    #[test]
    fn iter_next() {
        for &n in TEST_SIZE {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            let mut bv = BitVector::new();
            let mut vec = Vec::new();
            for _ in 0..n {
                let b = rng.gen_bool(0.5);
                vec.push(b);
                bv.push(b);

                assert_eq!(vec, bv.into_iter().collect::<Vec<_>>());
            }
        }
    }

    #[test]
    fn iter_nth() {
        for &n in TEST_SIZE {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            let mut bv = BitVector::new();
            let mut vec = Vec::new();
            for i in 0..n {
                let b = rng.gen_bool(0.5);
                vec.push(b);
                bv.push(b);

                let vec_val = vec.get(i as usize).copied();
                let itr_val = bv.into_iter().nth(i as usize);
                assert_eq!(vec_val, itr_val);
            }

            assert_eq!(None, bv.into_iter().nth(n as usize));
        }
    }
}
