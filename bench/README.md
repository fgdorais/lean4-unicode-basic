# Benchmarks

These programs time the UnicodeCLib lookups against other Unicode libraries. Every library looks
up the same input: 1,000,000 code points, each looked up 50 times, from five mixes:

- ASCII: random U+0020–007E;
- Latin: random U+00A0–024F (Latin-1 Supplement, Latin Extended-A and -B);
- CJK: random U+4E00–9FFF;
- mixed: random, 70% ASCII, 15% Latin, 7% Greek and Cyrillic, 8% CJK;
- text: the code points of `text/samples.txt`, the first article of the Universal Declaration of
  Human Rights in eleven languages (English, French, German, Polish, Greek, Russian, Arabic, Hindi,
  Chinese, Japanese and Korean).

`external.c` compares [ICU](https://icu.unicode.org/),
[utf8proc](https://github.com/JuliaStrings/utf8proc) and
[libunistring](https://www.gnu.org/software/libunistring/) from C, on general category, simple
uppercase, script, bidi class and canonical combining class. utf8proc has no script property.

`rust/` compares the Rust standard library and [ICU4X](https://github.com/unicode-org/icu4x)
from Rust, calling our C lookups through FFI. The standard library only has uppercase and the
`Alphabetic` and `Lowercase` properties. It also times a pass over UTF-8 text, one line of
`text/samples.txt` at a time, counting the alphabetic characters, with decoding included.

## Running

```sh
git clone https://github.com/JuliaStrings/utf8proc /path/to/utf8proc   # optional
UTF8PROC=/path/to/utf8proc bench/run.sh
cd bench/rust && cargo run --release
```

`run.sh` compiles `external.c` with the UnicodeCLib sources at `-O2` (set `CC` to choose the
compiler; `lean` must be on the path for `lean.h`). ICU and libunistring are loaded at run time from
the system (`libicuuc.so.N` or `libicucore.dylib`, `libunistring.so.N` or `libunistring.dylib`), so
no headers are needed; a library that is missing shows `-`.

`external.c` then repeats the C comparison with cold caches. Before each batch of 100 lookups, it
reads an 8 MB buffer, which evicts the tables from the L1 and L2 caches, and it times only the
batches. Each figure is the extra time per lookup over an empty batch. To evict the tables all the
way to memory, use a buffer larger than the last-level cache, with fewer batches to keep the run
short:

```sh
CC="cc -DJUNK_MB=1024 -DBATCHES=100" bench/run.sh
```

`rust/` needs Cargo and `lean` on the path. Before timing, it checks `Alphabetic` and `Lowercase`
against the other two on every code point and prints the number of disagreements.

## Results

2026-11-24, Linux x86-64 cloud container, ns per call. Differences under about 0.5 ns are noise,
and about 1.5 ns of each figure is the loop itself. The data versions differ (UnicodeBasic has
Unicode 18.0), which does not affect speed.

### C: gcc -O2, ICU 74, utf8proc 2.12.0, libunistring 1.1

| lookup          | input | ours | ICU | utf8proc | libunistring |
|-----------------|-------|-----:|----:|---------:|-------------:|
| general cat.    | ASCII | 1.9 | 1.9 | 1.9 | 3.4 |
|                 | Latin | 1.9 | 1.9 | 1.9 | 3.3 |
|                 | CJK   | 1.9 | 1.9 | 1.9 | 3.4 |
|                 | mixed | 1.9 | 2.3 | 1.9 | 3.4 |
|                 | text  | 1.9 | 1.9 | 1.9 | 3.5 |
| uppercase       | ASCII | 1.9 | 7.2 | 5.9 | 2.5 |
|                 | Latin | 1.9 | 9.1 | 8.5 | 2.5 |
|                 | CJK   | 1.9 | 3.1 | 2.0 | 2.8 |
|                 | mixed | 1.9 | 7.3 | 6.9 | 3.5 |
|                 | text  | 1.9 | 3.3 | 2.1 | 2.7 |
| script          | ASCII | 1.6 | 3.7 | - | 2.3 |
|                 | Latin | 1.6 | 3.7 | - | 2.3 |
|                 | CJK   | 1.7 | 3.7 | - | 2.3 |
|                 | mixed | 1.6 | 3.8 | - | 2.3 |
|                 | text  | 1.6 | 4.3 | - | 2.3 |
| bidi class      | ASCII | 2.0 | 2.8 | 1.7 | 3.9 |
|                 | Latin | 1.9 | 2.8 | 1.8 | 4.9 |
|                 | CJK   | 1.9 | 2.8 | 1.7 | 1.9 |
|                 | mixed | 1.9 | 2.8 | 1.7 | 5.4 |
|                 | text  | 1.9 | 2.9 | 1.7 | 2.8 |
| combining class | ASCII | 1.9 | 6.8 | 1.7 | 2.5 |
|                 | Latin | 1.9 | 6.7 | 1.7 | 2.5 |
|                 | CJK   | 1.9 | 6.8 | 1.7 | 2.5 |
|                 | mixed | 1.9 | 6.7 | 1.7 | 2.7 |
|                 | text  | 2.0 | 8.2 | 1.7 | 2.6 |

### C with cold caches

Our three-stage tables trade memory for simplicity (the C library is about 330 KB), so these runs
check what that costs when the tables are not already in cache. The figures below average two runs.

L1 and L2 evicted before each batch of 100 lookups (default settings; the two runs agree to within
about 1 ns):

| lookup          | input | ours | ICU | utf8proc | libunistring |
|-----------------|-------|-----:|----:|---------:|-------------:|
| general cat.    | ASCII | 1.5 | 2.2 | 1.8 | 2.7 |
|                 | Latin | 1.8 | 2.6 | 4.3 | 2.9 |
|                 | CJK   | 1.7 | 3.0 | 1.9 | 3.6 |
|                 | mixed | 1.8 | 2.8 | 4.1 | 3.4 |
|                 | text  | 1.1 | 2.2 | 2.5 | 3.1 |
| uppercase       | ASCII | 1.6 | 12.2 | 7.0 | 2.0 |
|                 | Latin | 2.4 | 15.1 | 13.1 | 2.4 |
|                 | CJK   | 1.9 | 3.0 | 2.0 | 3.3 |
|                 | mixed | 2.8 | 12.8 | 9.1 | 5.5 |
|                 | text  | 2.0 | 7.2 | 3.6 | 3.4 |
| script          | ASCII | 1.4 | 4.5 | - | 1.9 |
|                 | Latin | 1.8 | 6.0 | - | 2.2 |
|                 | CJK   | 2.0 | 6.0 | - | 2.6 |
|                 | mixed | 2.0 | 6.5 | - | 2.9 |
|                 | text  | 1.6 | 5.3 | - | 2.0 |
| bidi class      | ASCII | 1.4 | 2.0 | 2.2 | 2.7 |
|                 | Latin | 1.8 | 2.9 | 4.4 | 6.4 |
|                 | CJK   | 1.7 | 2.7 | 1.9 | 1.2 |
|                 | mixed | 1.4 | 2.5 | 4.6 | 7.7 |
|                 | text  | 1.5 | 2.2 | 3.1 | 3.5 |
| combining class | ASCII | 1.2 | 10.5 | 2.3 | 2.7 |
|                 | Latin | 1.8 | 10.5 | 4.5 | 3.0 |
|                 | CJK   | 1.7 | 11.3 | 1.6 | 3.4 |
|                 | mixed | 1.1 | 10.6 | 4.8 | 4.2 |
|                 | text  | 1.1 | 10.7 | 2.6 | 4.2 |

Tables evicted to memory before each batch of 100 lookups (`JUNK_MB=1024`, `BATCHES=100`, larger
than this machine's 260 MB L3; the two runs differ by up to about 5 ns, so the figures are rounded):

| lookup          | input | ours | ICU | utf8proc | libunistring |
|-----------------|-------|-----:|----:|---------:|-------------:|
| general cat.    | ASCII | 6 | 13 | 12 | 10 |
|                 | Latin | 8 | 15 | 23 | 9 |
|                 | CJK   | 7 | 19 | 9 | 14 |
|                 | mixed | 10 | 16 | 24 | 12 |
|                 | text  | 5 | 12 | 14 | 8 |
| uppercase       | ASCII | 9 | 22 | 19 | 9 |
|                 | Latin | 15 | 27 | 29 | 15 |
|                 | CJK   | 8 | 18 | 9 | 8 |
|                 | mixed | 20 | 27 | 31 | 17 |
|                 | text  | 9 | 23 | 17 | 11 |
| script          | ASCII | 6 | 17 | - | 8 |
|                 | Latin | 7 | 22 | - | 10 |
|                 | CJK   | 7 | 22 | - | 10 |
|                 | mixed | 11 | 33 | - | 13 |
|                 | text  | 7 | 18 | - | 10 |
| bidi class      | ASCII | 7 | 14 | 13 | 7 |
|                 | Latin | 7 | 16 | 22 | 11 |
|                 | CJK   | 6 | 16 | 8 | 6 |
|                 | mixed | 8 | 17 | 23 | 12 |
|                 | text  | 8 | 15 | 16 | 8 |
| combining class | ASCII | 5 | 36 | 13 | 8 |
|                 | Latin | 7 | 40 | 20 | 8 |
|                 | CJK   | 6 | 36 | 9 | 8 |
|                 | mixed | 9 | 43 | 24 | 9 |
|                 | text  | 4 | 36 | 14 | 9 |

Even when cold, our lookups stay at or below the others, except uppercase: libunistring ties
ours on Latin input and is about 3 ns faster on mixed input, where the many distinct case mappings
spread over more cache lines. A lookup is three dependent loads: `stage1`, which is small and
shared by all characters, then a row of `stage2` and an entry of `value`, which nearby characters
share.

### Rust: rustc 1.97 (std has Unicode 17.0), ICU4X 2.4

Our lookups are C functions called through FFI, so they are not inlined into the loop. ICU4X stores
enumerated properties in a code point trie, which Rust inlines, and binary properties as sorted
ranges, which it searches.

| lookup          | input | ours | std | ICU4X |
|-----------------|-------|-----:|----:|------:|
| general cat.    | ASCII | 2.0 | - | 1.0 |
|                 | Latin | 2.0 | - | 1.0 |
|                 | CJK   | 1.9 | - | 3.4 |
|                 | mixed | 1.9 | - | 2.0 |
|                 | text  | 1.9 | - | 1.4 |
| uppercase       | ASCII | 1.8 | 8.6 | 16.8 |
|                 | Latin | 1.6 | 38.6 | 18.9 |
|                 | CJK   | 1.6 | 24.3 | 8.7 |
|                 | mixed | 1.6 | 17.6 | 17.4 |
|                 | text  | 1.6 | 16.0 | 9.8 |
| script          | ASCII | 1.6 | - | 0.9 |
|                 | Latin | 1.8 | - | 1.5 |
|                 | CJK   | 1.6 | - | 4.0 |
|                 | mixed | 1.6 | - | 2.0 |
|                 | text  | 1.6 | - | 1.4 |
| bidi class      | ASCII | 1.6 | - | 1.0 |
|                 | Latin | 1.8 | - | 1.0 |
|                 | CJK   | 1.6 | - | 4.3 |
|                 | mixed | 1.6 | - | 1.9 |
|                 | text  | 1.6 | - | 1.4 |
| combining class | ASCII | 1.9 | - | 1.0 |
|                 | Latin | 1.9 | - | 1.6 |
|                 | CJK   | 1.9 | - | 4.2 |
|                 | mixed | 1.9 | - | 1.9 |
|                 | text  | 1.9 | - | 1.4 |
| alphabetic      | ASCII | 1.9 | 5.4 | 22.0 |
|                 | Latin | 1.9 | 20.4 | 21.6 |
|                 | CJK   | 1.9 | 9.0 | 20.9 |
|                 | mixed | 1.9 | 16.9 | 22.0 |
|                 | text  | 1.9 | 22.8 | 22.0 |
| lowercase       | ASCII | 1.7 | 3.8 | 26.1 |
|                 | Latin | 1.7 | 2.7 | 30.8 |
|                 | CJK   | 1.7 | 2.6 | 22.5 |
|                 | mixed | 1.6 | 6.8 | 26.2 |
|                 | text  | 1.7 | 1.5 | 22.2 |

UTF-8 text, counting alphabetic characters, ns per character with decoding included. The standard
library has fast paths for ASCII and for some ranges, which show in the first four languages.

| language | ours | std | ICU4X |
|----------|-----:|----:|------:|
| English  | 1.9 | 0.8 | 23.3 |
| French   | 1.9 | 1.3 | 22.5 |
| German   | 2.0 | 1.1 | 21.9 |
| Polish   | 1.9 | 1.7 | 22.3 |
| Greek    | 2.3 | 31.0 | 22.3 |
| Russian  | 2.2 | 32.5 | 22.5 |
| Arabic   | 2.2 | 41.4 | 22.0 |
| Hindi    | 2.3 | 69.8 | 23.0 |
| Chinese  | 2.4 | 11.6 | 22.6 |
| Japanese | 2.4 | 16.5 | 22.0 |
| Korean   | 2.2 | 50.8 | 22.2 |

The check found 0 disagreements with ICU4X and 12,978 with std, on 12,833 code points that were
all assigned in Unicode 18.0.

Through the Lean API, functions such as `getGC` add the cost of the call and of the Lean loop
around it, about 10 ns per call in the same setting.
