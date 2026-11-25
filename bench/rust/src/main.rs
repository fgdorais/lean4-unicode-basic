// Benchmark of the UnicodeCLib lookups against Rust's standard library and ICU4X.
// See `bench/README.md`.

use icu_casemap::CaseMapper;
use icu_properties::props::{
    Alphabetic, BidiClass, CanonicalCombiningClass, GeneralCategory, Lowercase, Script,
};
use icu_properties::{CodePointMapData, CodePointSetData};
use std::hint::black_box;
use std::time::Instant;

unsafe extern "C" {
    fn unicode_prop_lookup(c: u32) -> u64;
    fn unicode_case_lookup(c: u32) -> u64;
    fn unicode_script_lookup(c: u32) -> u32;
    fn unicode_bidi_class_lookup(c: u32) -> u64;
    fn unicode_combining_class_lookup(c: u32) -> u64;
}

// Bits of `unicode_prop_lookup`, from `UnicodeCLib/basic.h` and `UnicodeBasic/TableLookup.lean`
const GC_L: u64 = 0x1F;
const GC_LL: u64 = 0x2;
const GC_NL: u64 = 0x200;
const O_LOWER: u64 = 0x2_0000_0000;
const O_ALPHA: u64 = 0x4_0000_0000;

fn ours_alphabetic(c: char) -> bool {
    unsafe { unicode_prop_lookup(c as u32) & (O_ALPHA | GC_L | GC_NL) != 0 }
}
fn ours_lowercase(c: char) -> bool {
    unsafe { unicode_prop_lookup(c as u32) & (O_LOWER | GC_LL) != 0 }
}

const N: usize = 1_000_000;
const REPEAT: usize = 50;

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 as u32
    }
}

fn input(kind: usize, rng: &mut XorShift, text: &[char]) -> Vec<char> {
    (0..N)
        .map(|i| {
            let r = rng.next();
            let c = match kind {
                0 => 0x20 + r % 95,
                1 => 0xA0 + r % (0x250 - 0xA0),
                2 => 0x4E00 + r % (0xA000 - 0x4E00),
                3 => {
                    let k = r % 100;
                    let r = rng.next();
                    if k < 70 {
                        0x20 + r % 95
                    } else if k < 85 {
                        0xA0 + r % 0x1B0
                    } else if k < 92 {
                        0x391 + r % 0x200
                    } else {
                        0x4E00 + r % 0x5000
                    }
                }
                _ => text[i % text.len()] as u32,
            };
            char::from_u32(c).unwrap()
        })
        .collect()
}

/// Time `f` over `input`, in nanoseconds per call
fn time<T>(input: &[char], f: impl Fn(char) -> T) -> f64 {
    let t = Instant::now();
    for _ in 0..REPEAT {
        for &c in input {
            black_box(f(black_box(c)));
        }
    }
    t.elapsed().as_nanos() as f64 / (input.len() * REPEAT) as f64
}

/// Time `f` over every `char` of `s`, decoding UTF-8 on the fly, in nanoseconds per `char`
fn time_str(s: &str, f: impl Fn(char) -> bool) -> f64 {
    let t = Instant::now();
    let mut count = 0usize;
    for _ in 0..REPEAT {
        count += black_box(s).chars().filter(|&c| f(c)).count();
    }
    black_box(count);
    t.elapsed().as_nanos() as f64 / (s.chars().count() * REPEAT) as f64
}

fn cell(t: Option<f64>) -> String {
    t.map_or("-".into(), |t| format!("{t:.2}"))
}

fn row(name: &str, ours: f64, std: Option<f64>, icu4x: f64) {
    println!(
        "| {name:<15} | {ours:>7.2} | {:>7} | {icu4x:>7.2} |",
        cell(std)
    );
}

fn main() {
    let samples = std::fs::read_to_string("../text/samples.txt").expect("../text/samples.txt");
    let text: Vec<char> = samples.chars().collect();
    let gc = CodePointMapData::<GeneralCategory>::new();
    let script = CodePointMapData::<Script>::new();
    let bidi = CodePointMapData::<BidiClass>::new();
    let ccc = CodePointMapData::<CanonicalCombiningClass>::new();
    let alpha = CodePointSetData::new::<Alphabetic>();
    let lower = CodePointSetData::new::<Lowercase>();
    let cm = CaseMapper::new();

    // Sanity check: count disagreements, which come from different Unicode
    // versions
    let (mut std_diff, mut icu4x_diff) = (0, 0);
    for c in (0..=0x10FFFF).filter_map(char::from_u32) {
        std_diff += (ours_alphabetic(c) != c.is_alphabetic()) as u32;
        std_diff += (ours_lowercase(c) != c.is_lowercase()) as u32;
        icu4x_diff += (ours_alphabetic(c) != alpha.contains(c)) as u32;
        icu4x_diff += (ours_lowercase(c) != lower.contains(c)) as u32;
    }
    println!(
        "Alphabetic and Lowercase disagreements: {std_diff} with std, {icu4x_diff} with ICU4X"
    );
    println!("Rust std and ICU4X 2.4; ns per call, {N} code points x {REPEAT}");
    let mut rng = XorShift(88172645463325252);
    for (kind, name) in ["ASCII", "Latin", "CJK", "mixed", "text"]
        .iter()
        .enumerate()
    {
        let inp = input(kind, &mut rng, &text);
        println!(
            "\n{name}\n\n| {:<15} | {:>7} | {:>7} | {:>7} |\n|---|---|---|---|",
            "lookup", "ours", "std", "ICU4X"
        );
        row(
            "general cat.",
            time(&inp, |c| unsafe { unicode_prop_lookup(c as u32) }),
            None,
            time(&inp, |c| gc.get(c)),
        );
        row(
            "uppercase",
            time(&inp, |c| unsafe { unicode_case_lookup(c as u32) }),
            Some(time(&inp, |c| c.to_uppercase().next())),
            time(&inp, |c| cm.simple_uppercase(c)),
        );
        row(
            "script",
            time(&inp, |c| unsafe { unicode_script_lookup(c as u32) }),
            None,
            time(&inp, |c| script.get(c)),
        );
        row(
            "bidi class",
            time(&inp, |c| unsafe { unicode_bidi_class_lookup(c as u32) }),
            None,
            time(&inp, |c| bidi.get(c)),
        );
        row(
            "combining class",
            time(&inp, |c| unsafe {
                unicode_combining_class_lookup(c as u32)
            }),
            None,
            time(&inp, |c| ccc.get(c)),
        );
        row(
            "alphabetic",
            time(&inp, ours_alphabetic),
            Some(time(&inp, |c| c.is_alphabetic())),
            time(&inp, |c| alpha.contains(c)),
        );
        row(
            "lowercase",
            time(&inp, ours_lowercase),
            Some(time(&inp, |c| c.is_lowercase())),
            time(&inp, |c| lower.contains(c)),
        );
    }

    // UTF-8 pass: count the alphabetic chars of each line of the samples, repeated to about 64 KB
    println!("\nUTF-8 text, alphabetic count; ns per char, decoding included\n");
    println!(
        "| {:<8} | {:>7} | {:>7} | {:>7} |\n|---|---|---|---|",
        "language", "ours", "std", "ICU4X"
    );
    let langs = [
        "en", "fr", "de", "pl", "el", "ru", "ar", "hi", "zh", "ja", "ko",
    ];
    for (lang, line) in langs.iter().zip(samples.lines()) {
        let s = line.repeat(65536 / line.len() + 1);
        println!(
            "| {lang:<8} | {:>7.2} | {:>7.2} | {:>7.2} |",
            time_str(&s, ours_alphabetic),
            time_str(&s, |c| c.is_alphabetic()),
            time_str(&s, |c| alpha.contains(c))
        );
    }
}
