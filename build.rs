use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn main() {
    let out_dir = env::var("OUT_DIR").expect("no out directory");
    let dest = Path::new(&out_dir).join("build_constants.rs");

    let mut file = File::create(&dest).expect("could not create file");

    let size: usize = option_env!("DEBRA_EPOCH_CACHE_SIZE")
        .map_or(Ok(256), str::parse)
        .expect("failed to parse env variable DEBRA_EPOCH_CACHE_SIZE");

    if size == 0 {
        panic!("invalid DEBRA_EPOCH_CACHE_SIZE value (0)");
    } else if size > 4096 {
        panic!("invalid DEBRA_EPOCH_CACHE_SIZE value (too large)");
    }

    write!(&mut file, "const DEFAULT_BAG_SIZE: usize = {};", size)
        .expect("could not write to file");
}
