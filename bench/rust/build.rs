// Compile the UnicodeCLib lookups so that they can be called from Rust.
use std::process::Command;

fn main() {
    let prefix = Command::new("lean")
        .arg("--print-prefix")
        .output()
        .expect("lean not found");
    let prefix = String::from_utf8(prefix.stdout).unwrap();
    let mut build = cc::Build::new();
    build
        .include(format!("{}/include", prefix.trim()))
        .include("../../UnicodeCLib")
        .opt_level(2);
    for f in ["prop", "case", "script", "bidi_class", "combining_class"] {
        let path = format!("../../UnicodeCLib/{f}.c");
        println!("cargo:rerun-if-changed={path}");
        build.file(path);
    }
    build.compile("unicodeclib");
}
