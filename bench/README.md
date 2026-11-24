# Benchmarks

`external.c` times the UnicodeCLib lookups against [ICU](https://icu.unicode.org/) and
[utf8proc](https://github.com/JuliaStrings/utf8proc) on the same random input: 1,000,000 code
points, each looked up 50 times, for four mixes of input:

- ASCII: U+0020–007E;
- Latin: U+00A0–024F (Latin-1 Supplement, Latin Extended-A and -B);
- CJK: U+4E00–9FFF;
- mixed: 70% ASCII, 15% Latin, 7% Greek and Cyrillic, 8% CJK.

It compares general category, simple uppercase, script, bidi class and canonical combining class.
utf8proc has no script property.

## Running

```sh
git clone https://github.com/JuliaStrings/utf8proc /path/to/utf8proc   # optional
UTF8PROC=/path/to/utf8proc bench/run.sh
```

`run.sh` compiles `external.c` with the UnicodeCLib sources at `-O2` (set `CC` to choose the
compiler; `lean` must be on the path for `lean.h`). ICU is loaded at run time from the system
(`libicuuc.so.N` on Linux, `libicucore.dylib` on macOS), so no ICU headers are needed; without ICU
or utf8proc, their columns show `-`.

## Results

2026-11-24, Linux x86-64 cloud container, gcc -O2, ICU 74 (Unicode 15.1), utf8proc 2.12.0, ns
per call. The data versions differ (UnicodeBasic has Unicode 18.0), which does not affect speed.
Differences under about 0.5 ns are noise.

| lookup          | input | ours | ICU | utf8proc |
|-----------------|-------|-----:|----:|---------:|
| general cat.    | ASCII | 2.0 | 2.5 | 2.0 |
|                 | Latin | 2.0 | 2.1 | 2.0 |
|                 | CJK   | 1.9 | 1.9 | 1.9 |
|                 | mixed | 2.0 | 2.0 | 1.9 |
| uppercase       | ASCII | 1.9 | 7.4 | 6.4 |
|                 | Latin | 1.9 | 9.4 | 9.0 |
|                 | CJK   | 1.9 | 3.1 | 2.0 |
|                 | mixed | 1.9 | 7.2 | 6.5 |
| script          | ASCII | 1.6 | 3.8 | - |
|                 | Latin | 1.6 | 3.8 | - |
|                 | CJK   | 1.6 | 3.7 | - |
|                 | mixed | 2.7 | 4.1 | - |
| bidi class      | ASCII | 1.9 | 2.5 | 1.8 |
|                 | Latin | 1.9 | 2.5 | 2.0 |
|                 | CJK   | 1.9 | 2.5 | 1.7 |
|                 | mixed | 1.9 | 2.6 | 1.8 |
| combining class | ASCII | 1.9 | 8.2 | 2.0 |
|                 | Latin | 2.1 | 8.9 | 1.8 |
|                 | CJK   | 1.9 | 6.7 | 1.7 |
|                 | mixed | 1.9 | 7.7 | 1.8 |

Through the Lean API, functions such as `getGC` add the cost of the call and of the Lean loop
around it, about 10 ns per call in the same setting.
