/// Fully Indexable Dictionary of bits that supports rank and select operations.
pub trait FID {

    /// Returns the total number of bits.
    fn len(&self) -> u64;

    /// Returns true if the collection is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Compute the number of bits in `[0..i)`.
    fn rank(&self, b: bool, i: u64) -> u64 {
        if b {
            self.rank1(i)
        } else {
            self.rank0(i)
        }
    }

    /// Compute the number of zeroes in `[0..i)`.
    fn rank0(&self, i: u64) -> u64 {
        i - self.rank1(i)
    }

    /// Compute the number of ones in `[0..i)`.
    fn rank1(&self, i: u64) -> u64 {
        i - self.rank0(i)
    }

    /// Locate the position of the `(r + 1)`-th bit.
    fn select(&self, b: bool, r: u64) -> u64 {
        let (mut s, mut e) = (0, self.len());

        while e - s > 1 {
            let m = (s + e) / 2;
            let rank = self.rank(b, m);
            if r < rank {
                e = m
            } else {
                s = m
            }
        }
        s
    }

    /// Locate the position of the `(r + 1)`-th zero.
    fn select0(&self, r: u64) -> u64 {
        self.select(false, r)
    }

    /// Locate the position of the `(r + 1)`-th one.
    fn select1(&self, r: u64) -> u64 {
        self.select(true, r)
    }

    /// Returns the `i`-th bit.
    fn get(&self, i: u64) -> bool {
        self.rank1(i + 1) - self.rank1(i) > 0
    }

    /// Gets a slice with `size` bits at position `i`.
    ///
    /// # Panics
    /// * End position of the slice exceeds the capacity.
    /// * `size` is greater than 64.
    fn get_slice(&self, i: u64, size: u64) -> u64 {
        let mut bits = 0;
        for j in 0..size {
            let bit = self.get(i + j) as u64;
            bits |= bit << j;
        }
        bits
    }

    /// Gets the `i`-th word with `size` bits.
    ///
    /// # Panics
    /// * End position of the word exceeds the capacity.
    /// * `size` is greater than 64.
    fn get_word(&self, i: u64, size: u64) -> u64 {
        self.get_slice(i * size, size)
    }
}
