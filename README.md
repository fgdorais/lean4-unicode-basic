# Lean 4 / Unicode Basic

Lightweight Unicode support for Lean 4.

Unicode properties that are currently supported are:

* `Alphabetic`
* `Bidi_Class`, `Bidi_Control`, and `Bidi_Mirrored`
* `Canonical_Combining_Class`
* `Uppercase`, `Lowercase`, `Cased` and `Case_Ignorable`
* `Decomposition_Type` and `Decomposition_Mapping`
* `General_Category`
* `Hex_Digit`
* `Math`
* `Name`
* `Numeric_Type` and `Numeric_Value`
* `Simple_Lowercase_Mapping`, `Simple_Uppercase_Mapping`, and `Simple_Titlecase_Mapping`
* `White_Space`

To keep the library lightweight, only properties that can be derived exclusively from `UnicodeData.txt` and `PropList.txt` can be supported.
If you need a property not yet in the list above, please submit a feature request!

## Installation

Add the following dependency to your project's `lakefile.lean`:

```lean
require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic" @ "main"
```

Then add `import UnicodeBasic` at the top of any Lean file where you plan to use this library.

Use the branch `"docs"` instead of `"main"` if you need to have local library documentation. ([doc-gen4](https://github.com/leanprover/doc-gen4) cannot be used directly because of a circular dependency.)

## Documentation

Documentation for the library is located at [dorais.org/lean4-unicode-basic/docs/](https://www.dorais.org/lean4-unicode-basic/docs/).

The main entry point is the root file [`UnicodeBasic.lean`](https://www.dorais.org/lean4-unicode-basic/docs/UnicodeBasic.lean). This file contains a description of the main API as well as all primary library functions. The file [`UnicodeBasic/Types.lean`](https://www.dorais.org/lean4-unicode-basic/docs/UnicodeBasic/Types.lean) contains all the primary data types used in the library.

The remaining files are implementation details. Some of these may be of interest for developers. For example [`UnicodeBasic/CharacterDatabase.lean](https://www.dorais.org/lean4-unicode-basic/docs/UnicodeBasic/CharacterDatabase.lean) defines a stream type for parsing files from the [Unicode Character Database](https://www.unicode.org/Public/UCD/latest/ucd/).

-----

* The `Lean 4 / Unicode Basic` library is copyright © 2023 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
* The `UnicodeData.txt` and `PropList.txt` files are copyright © 1991-2023 Unicode, Inc. The files are distributed under the [Unicode® Copyright and Terms of Use](https://www.unicode.org/copyright.html). See the file LICENSE-UNICODE for additional details.
