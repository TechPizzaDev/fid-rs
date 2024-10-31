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
const MAX_CODE_SIZE: usize = 48;

fn main() {
    let mut combination = vec![vec![0u64; SBLOCK_WIDTH + 1]; SBLOCK_WIDTH + 1];
    for n in 0..=SBLOCK_WIDTH {
        combination[n][0] = 1;
        for r in 1..=n {
            combination[n][r] = combination[n - 1][r - 1] + combination[n - 1][r];
        }
    }

    let mut code_size = vec![0; SBLOCK_WIDTH + 1];
    let mut avg_code_size = vec![0; SBLOCK_WIDTH + 1];

    code_size[0] = 0;
    avg_code_size[0] = 0;
    code_size[SBLOCK_WIDTH] = 0;
    avg_code_size[SBLOCK_WIDTH] = 0;

    for n in 1..SBLOCK_WIDTH {
        let size = log2(combination[SBLOCK_WIDTH][n] - 1) as usize + 1;
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

    let out_dir = "src";
    let out_path = Path::new(&out_dir).join("tables.rs");
    let mut f = File::create(&out_path).unwrap();

    writedoc!(
        f,
        "
        pub const SBLOCK_WIDTH: u64 = {:?};
        const SIZE: usize = SBLOCK_WIDTH as usize + 1;
        pub const COMBINATION: [[u64; SIZE]; SIZE] = {:?};
        pub const CODE_SIZE: [u8; SIZE] = {:?};
        pub const AVG_CODE_SIZE: [u8; SIZE] = {:?};
        ",
        SBLOCK_WIDTH,
        combination,
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
