# Lean 4 / Unicode Basic

Basic Unicode support for Lean 4.

Unicode properties that are currently supported by `UnicodeBasic` include:

* `Alphabetic`
* `Bidi_Class`
* `Bidi_Control`
* `Bidi_Mirrored`
* `Canonical_Combining_Class`
* `Case_Folding`
* `Case_Ignorable`
* `Cased`
* `Decomposition_Mapping`
* `Decomposition_Type`
* `Default_Ignorable_Code_Point`
* `General_Category`
* `Hex_Digit`
* `Lowercase`
* `Math`
* `Name`
* `Noncharacter_Code_Point`
* `Numeric_Type`
* `Numeric_Value`
* `Script`
* `Script_Extensions`
* `Simple_Case_Folding`
* `Simple_Lowercase_Mapping`
* `Simple_Titlecase_Mapping`
* `Simple_Uppercase_Mapping`
* `Uppercase`
* `White_Space`

To keep the `UnicodeBasic` library lightweight, only commonly used properties can be supported. If you need a property not yet in the list above, please submit a feature request!

## The `lean4-unicode-*` family

This library is one of a small family of Lean 4 Unicode libraries. Each one has a narrow job, so
you only depend on what you need.

| Library | What it is for |
| --- | --- |
| **UnicodeBasic** (this library) | The foundation. Fast lookups of commonly used character properties such as general category, case mappings, numeric values, scripts and names, from compact precompiled tables. Start here. |
| [UnicodeData](https://github.com/fgdorais/lean4-unicode-data) | Direct access to the Unicode Character Database files themselves, such as `UnicodeData.txt`, `PropList.txt`, `CaseFolding.txt` and `SpecialCasing.txt`. Heavier than UnicodeBasic, but complete, and handy for properties UnicodeBasic does not cover or for checking it against the source. |
| [UnicodeFormat](https://github.com/fgdorais/lean4-unicode-format) | Encoding and decoding: UTF-8, UTF-16 and UTF-32, the byte-level encoding schemes with byte order marks, strict and lossy decoding, and streaming iterators. |
| [UnicodeLemmas](https://github.com/fgdorais/lean4-unicode-lemmas) | Proofs about UnicodeBasic properties, such as the fact that every cased character is alphabetic. |
| [UnicodeExtra](https://github.com/fgdorais/lean4-unicode-extra) | Unicode algorithms on whole strings that are too large or too specialized for UnicodeBasic, built on top of it. |

## Installation

Add the following dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "UnicodeBasic"
git = "https://github.com/fgdorais/lean4-unicode-basic.git"
rev = "main" # or any specific revision
```

Or this dependency to your project's `lakefile.lean`:

```lean4
require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic.git" @ "main"
```

Then add `import UnicodeBasic` at the top of any Lean file where you plan to use this library.

## Usage

The main entry point is the root file `UnicodeBasic`. This file contains a description of the main API as well as all primary library functions. The file `UnicodeBasic.Types` contains all the primary data types used in the library.

The remaining files are implementation details. Some of these may be of interest for developers. For example `UnicodeBasic.CharacterDatabase` defines a stream type for parsing files from the [Unicode Character Database](https://www.unicode.org/Public/UCD/latest/ucd/).

## Documentation

Current documentation can be found at [www.dorais.org/lean4-unicode-basic/doc](https://www.dorais.org/lean4-unicode-basic/doc/).
Documentation is also provided for each release since version 1.1.0.

Users can also generate documentation locally using `lake build UnicodeBasic:docs` in the `docs` directory.

-----

* The `Lean 4 / Unicode Basic` library is copyright © 2023-2026 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
* The Unicode Character Database files are copyright © 1991-2026 Unicode®, Inc. The data tables in the `data` directory are derived from these files. The files are distributed under the [Unicode® Copyright and Terms of Use](https://www.unicode.org/copyright.html). See the file LICENSE-UNICODE for additional details.
