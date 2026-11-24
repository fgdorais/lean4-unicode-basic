# How UnicodeBasic's tables are made and used

This is a guide for developers of UnicodeBasic and of the other Lean4 / Unicode libraries that
follow the same scheme. It is not part of the public API: everything described here may change
without notice. Users should only rely on the functions in `UnicodeBasic`.

UnicodeBasic has no dependencies and never reads the Unicode Character Database (UCD) at run time
or build time. Instead, a separate package in `util/` reads the UCD through
[UnicodeData](https://github.com/fgdorais/lean4-unicode-data) and writes two kinds of compact
tables, plus Lean copies of the C tables, all committed to the repository:

| Output | Written by | Read by | Used for |
| --- | --- | --- | --- |
| `data/*.txt` | `util/MakeTables.lean` | `UnicodeBasic/TableLookup.lean`, via `include_str` | Most properties |
| `UnicodeCLib/*.c` (except `basic.c`) | `util/MakeCLib.lean` | `UnicodeBasic/TableLookup.lean`, via `@[extern]` | Properties with values of at most 64 bits: general category, `Other_*` bits, simple case mappings, script, bidi class, bidi mirrored, canonical combining class, default ignorable, numeric value |
| `UnicodeBasic/Internal/*Tree.lean` | `util/MakeCLib.lean` | The kernel, through the bodies of the `CLib` lookups | Proofs by `decide +kernel` about the same properties |

The data flow is:

```
UCD files (in UnicodeData's data/ucd/)
   │  UnicodeData parses them (UnicodeData.data, PropList, CaseFolding, …)
   ▼
util/MakeTables  ──►  data/<Property>.txt  ──include_str──►  TableLookup.lookup*  ──►  public API
util/MakeCLib    ──►  UnicodeCLib/*.c      ──@[extern]────►  TableLookup.CLib.*  ──►  public API
```

Generated files are never edited by hand. Change the generator and regenerate.

## 1. The `util` package

`util/` is its own Lake package (`util/lakefile.toml`). It requires UnicodeData from git and
UnicodeBasic by path (`path = ".."`). Its library `Builders` holds the `mk*` functions that read
the UCD and build compressed tables, shared by its three executables:

- `MakeTables`: writes `../data/<Property>.txt`.
- `MakeCLib`: writes the C tables in `../UnicodeCLib/` and their kernel copies in
  `../UnicodeBasic/Internal/`.
- `TestTables`: checks the public API against UnicodeData (see section 6).

`util` pins its own `lean-toolchain` and commits its own `lake-manifest.json`, so the UCD version
the tables are built from is whatever UnicodeData revision that manifest names. The Update Util
workflow (`.github/workflows/update-util.yml`) updates that pin when UnicodeData's `main` moves. By
hand: copy UnicodeData's `lean-toolchain` into `util/lean-toolchain` and run `lake update` in
`util`.

To regenerate everything:

```sh
cd util
lake exe MakeTables     # all tables in data/
lake exe MakeCLib       # all C tables in UnicodeCLib/
lake exe TestTables     # must print nothing and exit 0
```

Both generators use paths relative to `util/`, so run them from there.

`MakeTables` takes property names as arguments (`lake exe MakeTables Name White_Space`). With no
arguments it writes the tables the library uses:

`Canonical_Decomposition_Mapping`, `Case_Folding`, `Decomposition_Mapping`, `Name`,
`Script_Extensions`, `Script_Name`, `Special_Casing`, `White_Space`.

It also knows a few more (`Alphabetic`, `Bidi_Class`, `Bidi_Mirrored`, `Canonical_Combining_Class`,
`Case_Mapping`, `Cased`, `Default_Ignorable_Code_Point`, `General_Category`, `Lowercase`, `Math`,
`Noncharacter_Code_Point`, `Numeric_Value`, `Other`, `Other_*`, `Prepended_Concatenation_Mark`,
`Titlecase`, `Uppercase`, `Variation_Selector`). These are not read by the library, which gets
those properties from the C tables or computes them, but they are handy for inspecting the data.
Each run prints the table size as `Size: <rows> + <extra code points covered by ranges>`.

## 2. The `data/*.txt` format

Every table is a plain text file in the UCD's own syntax, so the library's `UCDStream` parser
(`UnicodeBasic/CharacterDatabase.lean`) reads it:

- One record per line, fields separated by `;`. White space around fields is ignored.
- No comments and no blank lines (the parser would skip them, but the generators never write them).
- Code points are uppercase hexadecimal with at least four digits and no `U+`
  (`toHexStringRaw`), for example `00C0`, `1F600`, `10FFFF`.
- Records are sorted by their first field, strictly increasing, and ranges never overlap.
  The lookup code depends on this.
- Absent values are empty fields, not a sentinel. The library supplies the default (see
  section 4).

There are three record shapes.

**Range property tables** (binary properties): `start;stop`, or `start;` for a single code point.
Code points in some range have the property; all others do not. Adjacent ranges are merged.

```
0009;000D
0020;
0085;
```

Used by `White_Space`. (The public `isWhiteSpace` currently computes the property directly, so
only `lookupWhiteSpace` reads `White_Space.txt`.)

**Range data tables**: `start;stop;value…`, or `start;;value…` for a single code point. Every code
point in the range has the same value. Adjacent ranges with equal values are merged.

```
0000;0008;BN
0009;;S
000A;;B
```

Used by `Name` and `Script_Extensions`. (The example is `MakeTables Bidi_Class`, which the library
no longer reads.)

**Point tables**: `code;value…`, one record per code point that has a non-default value.

```
00A0;<noBreak>;0020
00A8;<compat>;0020;0308
```

Used by `Canonical_Decomposition_Mapping`, `Case_Folding`, `Decomposition_Mapping`,
`Script_Name` and `Special_Casing`.

### Compression

Tables are always compressed as far as the data allows. Besides merging adjacent ranges, the
generators fold anything the library can compute back:

- `First>`/`Last>` pairs in `UnicodeData.txt` become one range.
- Runs of names derived from the code point become one range with a lowercase tag, and
  `lookupName` rebuilds the name: `<control>`, `<private use>`, `<noncharacter>`, `<surrogate>`,
  `<cjk unified ideograph>`, `<cjk compatibility ideograph>`, `<hangul syllable>`,
  `<khitan small script character>`, `<egyptian hieroglyph>`, `<nushu character>`,
  `<tangut component>`, `<tangut ideograph>`, `<jurchen character>`, `<seal character>`.
  Tags are lowercase; the names the library returns follow the Standard's casing exactly
  (for example `CJK UNIFIED IDEOGRAPH-4E00`, `<control-0000>`).
- `Canonical_Decomposition_Mapping` stores the full (recursive) canonical decomposition, so the
  lookup needs no recursion. `Decomposition_Mapping` stores the single-step mapping with its
  compatibility tag (`<font>`, `<compat>`, …), or an empty tag field for canonical mappings.
- `Case_Folding` is `code;simple;full`, one record per code point in `CaseFolding.txt`:
  `simple` is empty when there is no simple (`C` or `S`) folding, and `full` is empty unless the
  full (`F`) folding has two or more code points.
- `Special_Casing` is `code;lower;title;upper`, unconditional mappings only, with each field empty
  when it agrees with the simple mapping from `UnicodeData.txt`.
- `Script_Extensions` values are space-separated script codes (see below), sorted by code.
  `Script_Name` maps a script code to its long name.
- Hangul syllables (names and decompositions) and `Noncharacter_Code_Point` are not in any
  table. They are computed in `UnicodeBasic/Hangul.lean` and `TableLookup` from their
  algorithmic definitions.

**Script codes.** A `Script` is its four-letter ISO 15924 code packed big-endian into a `UInt32`,
one ASCII byte per letter: `Latn` is `0x4C61746E`. Tables write the code in hex.

## 3. The C tables

For the properties every string operation touches, a Lean binary search over a parsed array is
too slow, so `MakeCLib` writes them as static C arrays. Each file has the same shape:

```c
typedef struct { uint32_t cmin; uint32_t cmax; uint64_t data; } unicode_data_t;  // basic.h
static const unicode_data_t table[TABLE_SIZE] = { {cmin, cmax, data}, … };
uint64_t unicode_xxx_lookup(uint32_t c);  // binary search on cmin, then check c <= cmax
```

Rows are sorted and non-overlapping, with values written as `UINT32_C(…)`/`UINT64_C(…)` decimal
literals. A code point outside every row gets the function's default.

- **`case.c`**, `unicode_case_lookup`: `data` packs the simple uppercase, lowercase and titlecase
  mappings, 21 bits each: bits 0–20 uppercase, 21–41 lowercase, 42–62 titlecase. Missing
  mappings are filled in with the code point itself (titlecase defaults to uppercase). Only code
  points with some mapping have a row; the default is `0`, which `lookupCaseMapping` reads as
  "maps to itself".
- **`script.c`**, `unicode_script_lookup`: `data` is the script code. Rows come straight from
  `Scripts.txt`. Default: `Zzzz` (Unknown).
- **`prop.c`**, `unicode_prop_lookup`: `data` low 32 bits hold the `GC` bit mask (one bit per
  general category, as in `basic.h` and `UnicodeBasic.Types`), high 32 bits hold
  `Other_Uppercase` (bit 32), `Other_Lowercase` (33), `Other_Alphabetic` (34) and `Other_Math` (35).
  Default: `Cn`.
- **`bidi_class.c`**, `unicode_bidi_class_lookup`: `data` is the index of the class in
  `CLib.bidiClasses` (the constructor order of `BidiClass`). Default: `BN`.
- **`combining_class.c`**, `unicode_combining_class_lookup`: `data` is the class. Default: `0`.
- **`bidi_mirrored.c`** and **`default_ignorable.c`**: one row per range with the property, with
  `data` `1`. Default: `0`.
- **`numeric.c`**, `unicode_numeric_lookup`: bits 0–1 are `1` for `Numeric_Type=Decimal`, `2` for
  `Digit` and `3` for `Numeric`. A run of consecutive decimal or digit values is one row, with
  bits 2–22 the first code point of the run and bits 23–26 its value, so that the value of `c` is
  `c - first + value`. For `Numeric`, bit 2 is the sign, bits 3–11 the denominator (`0` for none)
  and bits 12–51 the absolute value of the numerator. Default: `0` (no numeric value).

These five files come from one generic writer, `makeTableC`, which drops rows with the default
value and merges adjacent rows with equal data.

`prop.c` also folds alternating case pairs. A run like `Lu Ll Lu Ll …` (Latin Extended-A, Greek,
Cyrillic) is stored as one row whose category is the union `LC` (= `Lu|Ll|Lt`), with bit 31 saying
which parity is uppercase: if `(c & 1) == bit31` the code point is `Lu`, otherwise `Ll`. The same
trick folds alternating `Ps`/`Pe` runs (stored as `PG`) and `Pi`/`Pf` runs (stored as `PQ`). The
lookup decodes this, so callers always get exactly one category bit. Bit 31 and the union masks
are never returned.

`basic.h` holds the shared struct, the `UNICODE_GC_*` masks (which must match `GC` in
`UnicodeBasic/Types.lean`) and the prototypes. `basic.c` is hand-written (script abbreviation
conversions) and is not generated.

**Kernel copies of the C tables.** For each C table `foo.c`, `MakeCLib` also writes
`UnicodeBasic/Internal/FooTree.lean` (for example `PropTree.lean`, `BidiClassTree.lean`) with the
same rows as a B-tree `Internal.fooTree : Internal.BTree Nat`. A tree follows the C binary search: each internal node
`node key left right` is one step of it, with `key` the `cmin` of the middle row, and the search
continues in a leaf once at most 64 rows are left. A leaf `leaf lo hi keys block` holds rows `lo`
to `hi - 1`, with their `cmin` and `cmax` packed 42 bits per row in `keys` and their C data packed
in `block`: 63 bits per row for `case`, 36 for `prop`, 32 for `script`, 5 for `bidi_class`, 8 for
`combining_class`, 52 for `numeric` and 1 for `bidi_mirrored` and `default_ignorable`. `Internal.BTree` (in
`UnicodeBasic/Internal/BTree.lean`) is generic in the block type, so tables whose values are not
numbers can use it too. The trees are `noncomputable` so that programs never build them.

`lakefile.lean` compiles every `UnicodeCLib/*.c` with the system C compiler into a static
`libunicodeclib`, links it into the library (`moreLinkObjs`), and declares it as an `extern_lib`
so that precompiled modules of downstream packages find the symbols too.

## 4. Reading the tables: `UnicodeBasic.TableLookup`

`TableLookup` is internal. Its `lookup*` functions take raw `UInt32` code points and are not public
API.

**Text tables.** Each `lookupX` has a `where` clause with

```lean
  str : String := include_str "../data/X.txt"
  table : Thunk <| Array (UInt32 × UInt32 × α) := parseDataTable str fun start stop fields => …
```

`include_str` embeds the file in the compiled module. The `Thunk` defers parsing until the first
lookup, so programs pay only for the tables they use. There are three parsers, one per record
shape: `parsePropTable` (`Array (UInt32 × UInt32)`), `parseDataTable`
(`Array (UInt32 × UInt32 × α)`, with an empty `stop` read as `start`) and `parseTable`
(`Array (UInt32 × α)`). Each takes a function that turns the remaining fields into the value type.

A lookup is then always the same three steps:

1. If `c` is below the first row's start, return the default.
2. Binary search (`find`) for the last row whose start is `≤ c`.
3. If `c` is inside that row (`c ≤ stop` for ranges, `c == start` for point tables), decode its
   value; otherwise return the default.

Defaults: decompositions → the code point itself / `none`, case folding and special casing →
"no change", binary properties → `false`, `Script_Extensions` → the singleton set of
`lookupScript c`, `Name` → `<reserved-XXXX>`.

**C tables.** `TableLookup.CLib` declares the C functions as `@[extern]` definitions
(`lookupProp`, `lookupCase`, `lookupScript`, `lookupBidiClass`, `lookupBidiMirrored`,
`lookupCombiningClass`, `lookupDefaultIgnorable`, `lookupNumeric`), plus the `Other_*` bit masks.
The body of each does the same lookup as the C table in pure Lean on its B-tree, for example
`CLib.lookupPropIn Internal.propTree c.toNat`; the simpler tables share `CLib.lookupIn`, which
takes the data width and the default. The `lookup*` functions outside `CLib` decode the C data
into the library's types. Compiled code calls C, and the kernel unfolds the body, so `decide +kernel` can prove
facts such as `GeneralCategory.isLetter 'é' = true` or `getUpperChar 'é' = 'É'`. The derived
properties are bit tests on one `lookupProp` call, for example

```lean
lookupAlphabetic c = (CLib.lookupProp c &&& (oAlpha ||| (GC.L ||| GC.Nl))) != 0
```

and `lookupCased`, `lookupLowercase`, `lookupUppercase`, `lookupMath` work the same way.

## 5. The public API on top

The functions in `UnicodeBasic.lean` take `Char`, call the matching `lookup*` on `char.val`, and
convert the result to the public type. Many add a small ASCII shortcut before the lookup
(`getGC` uses a 128-entry array; case mappings and `isWhiteSpace` test ranges directly). Some
properties need no table at all: `isBidiControl`, `isHexDigit` and `isNoncharacterCodePoint` are
short range tests, and `isWhiteSpace` uses the general category plus U+0085.

Docstrings on these functions describe behavior and name the Unicode property they implement. They
never mention tables, encodings or shortcuts; implementation notes go in `--` comments.

## 6. Testing

`util/TestTables` streams every record of `UnicodeData.txt` (skipping surrogates, which are not
`Char`s) and compares the **public** function (`getGC`, `isAlphabetic`, `getName`, …) against the
value UnicodeData computes from the UCD. It does not test the `lookup*` functions directly. Run all
tests with `lake exe TestTables` in `util`, or a few by name (`lake exe TestTables Name`). Any
mismatch prints `Error: <test> <code point>` and the exit code is 1. CI builds `util` and runs it
on every pull request.

The `*Tree` tests (`PropTree`, `BidiClassTree`, …) are the exception: each compares the Lean lookup
(`CLib.lookupPropIn`, `CLib.lookupBidiClassIn`, …) on a computable copy of its tree with the C
lookup on every code point, since nothing proves they agree. `TestTables` also has a few
`decide +kernel` examples, which fail to build if the kernel can no longer reduce property lookups.

## 7. Adding a table

To add a property `Foo` in the same style (in this repo or a sibling library):

1. In the generator, write `mkFoo` that reads the UCD through UnicodeData and returns a sorted,
   merged array of ranges or points. Fold anything computable into ranges or leave it out.
2. Add a `"Foo"` case to `main` that writes `../data/Foo.txt` in one of the three record shapes,
   and add `"Foo"` to the default argument list.
3. Run the generator and commit `data/Foo.txt`.
4. In the library, add `lookupFoo (c : UInt32)` with a `where` clause that `include_str`s the file
   into a `Thunk` with the matching parser, and the three-step lookup above with a sensible
   default. Mark it internal.
5. Add the public `getFoo`/`isFoo (char : Char)` with a behavioral docstring.
6. Add a `testFoo` to `TestTables` that checks the public function against UnicodeData.

A property whose values fit in 64 bits can go in a C table instead, which saves the first-call
parse and lets the kernel evaluate it. Build its rows (sorted, non-overlapping, data as a
`UInt64`) in `MakeCLib`, add it to the `makeTableC`/`makeTreeLean` list in `main`, add the
prototype to `basic.h`, and regenerate. In `TableLookup`, add a `CLib.lookupFooIn` on
`CLib.lookupIn` and an `@[extern]` `CLib.lookupFoo` whose body is `CLib.lookupFooIn
Internal.fooTree c.toNat`, then decode it in `lookupFoo`. Add a `FooTree` test and a
`decide +kernel` example to `TestTables`.

## 8. Updating to a new Unicode version

1. UnicodeData updates its `data/ucd/` files.
2. Update `util`'s pin (the Update Util workflow does this daily).
3. Regenerate: `lake exe MakeTables && lake exe MakeCLib` in `util`.
4. Check the diff. New derived-name blocks (for example a new `… CHARACTER-XXXX` range) show up as
   thousands of new `Name.txt` lines and need a new tag in `MakeTables.mkName` and a new case in
   `lookupName`. New compatibility tags need a case in `lookupDecompositionMapping?`.
5. Run `lake exe TestTables`, then build the library with `lake build --wfail`.
