use std::fs::File;
use std::io::Write;
use std::path::Path;

use distrs::Normal;
use indoc::writedoc;
use roxygen::*;

const fn log2(x: u64) -> u32 {
    (u64::BITS - 1) - (x | 1).leading_zeros()
}

const SBLOCK_WIDTH: usize = 64;
const SIZE: usize = SBLOCK_WIDTH + 1;
const MAX_CODE_SIZE: usize = 48;

/// Padding the arrays eliminates bound checks and allows unrolling around 7-bit codewords;
/// lookups outside the range are invalid and simply return zero.
const PADDED_WIDTH: usize = 1 << 7;

fn main() {
    assert!(PADDED_WIDTH >= SIZE);

    let mut comb = Box::new([0u64; SIZE * SIZE]);

    fn row(comb: &mut [u64; SIZE * SIZE], n: usize) -> &mut [u64; SIZE] {
        let start = n * SIZE;
        let end = start + SIZE;
        (&mut comb[start..end]).try_into().unwrap()
    }

    for n in 0..SIZE {
        row(&mut comb, n)[0] = 1;
        for r in 1..=n {
            let prev_rank = row(&mut comb, n - 1);
            row(&mut comb, n)[r] = prev_rank[r - 1] + prev_rank[r];
        }
    }

    let mut code_size = vec![0; PADDED_WIDTH];
    let mut avg_code_size = vec![0; SBLOCK_WIDTH];

    for n in 1..SBLOCK_WIDTH {
        let size = log2(row(&mut comb, SBLOCK_WIDTH)[n] - 1) as usize + 1;
        code_size[n] = if size <= MAX_CODE_SIZE {
            size
        } else {
            SBLOCK_WIDTH
        } as u8;
    }

    for n in 1..SBLOCK_WIDTH {
        let probability = n as f64 / SBLOCK_WIDTH as f64;
        avg_code_size[n] = code_size_upper_bound(probability, SBLOCK_WIDTH, &code_size);
    }

    let out_dir = Path::new(&"src");
    let mut src_file = File::create(&out_dir.join("tables.rs")).unwrap();

    writedoc!(
        src_file,
        "
        pub const SBLOCK_WIDTH: u64 = {:?};
        const SIZE: usize = SBLOCK_WIDTH as usize + 1;
        const PADDED_WIDTH: usize = {:?};
        pub const COMBINATION: [u64; SBLOCK_WIDTH as usize * SIZE] = {:?};
        pub const CODE_SIZE: [u8; PADDED_WIDTH] = {:?};
        pub const AVG_CODE_SIZE: [u8; SBLOCK_WIDTH as usize] = {:?};
        ",
        SBLOCK_WIDTH,
        PADDED_WIDTH,
        &comb[..(SBLOCK_WIDTH as usize * SIZE)],
        code_size,
        avg_code_size
    )
    .unwrap();
}

#[roxygen]
/// Estimate an upper bound for the number of bits required for enumerative coding
/// using a Gaussian approximation to the binomial distribution.
fn code_size_upper_bound(
    /// Probability (between 0 and 1) that a single bit is true.
    p: f64,
    /// Total number of bits in the integer.
    n_bits: usize,
    /// Precomputed array of code sizes indexed by the number of true bits (popcount).
    code_size: &[u8],
) -> u8 {
    let mean_popcount = n_bits as f64 * p;
    let std_dev_popcount = (n_bits as f64 * p * (1.0 - p)).sqrt();

    let expected_bits: f64 = (0..n_bits)
        .into_iter()
        .map(|k| {
            let lower_prob = Normal::cdf(k as f64 - 0.5, mean_popcount, std_dev_popcount);
            let upper_prob = Normal::cdf(k as f64 + 0.5, mean_popcount, std_dev_popcount);
            let binom_prob = upper_prob - lower_prob;
            binom_prob * code_size[k as usize] as f64
        })
        .sum();

    // Truncating the estimation makes it inaccurate at the edges,
    // so nudge it up with a U-shaped parabola centered at 0.5.
    let offset = (p - 0.5) * (p - 0.5);

    return (expected_bits + offset).ceil() as u8;
}
