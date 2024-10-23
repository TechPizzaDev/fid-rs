use std::fs::File;
use std::io::Write;
use std::path::Path;

use indoc::formatdoc;

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

    code_size[0] = 0;
    code_size[SBLOCK_WIDTH] = 0;

    for n in 1..SBLOCK_WIDTH {
        let size = log2(combination[SBLOCK_WIDTH][n] - 1) as usize + 1;
        code_size[n] = if size <= MAX_CODE_SIZE {
            size
        } else {
            SBLOCK_WIDTH
        } as u8;
    }

    let out_dir = "src";
    let out_path = Path::new(&out_dir).join("tables.rs");
    let mut f = File::create(&out_path).unwrap();

    f.write_all(
        formatdoc!(
            "pub const COMBINATION: [[u64; {size}]; {size}] = {:?};
            pub const CODE_SIZE: [u8; {size}] = {:?};",
            combination,
            code_size,
            size = SBLOCK_WIDTH + 1
        ).as_bytes(),
    ).unwrap();
}
