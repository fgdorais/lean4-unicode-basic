# UnicodeData for Lean 4

Basic and lightweight Unicode support for Lean 4.

Unicode properties that are currently supported are:

* `Bidi_Class` and `Bidi_Mirrored`
* `Canonical_Combining_Class`
* `Decomposition_Type` and `Decomposition_Mapping`
* `General_Category`
* `Name` (except for Hangul Syllables)
* `Numeric_Type` and `Numeric_Value`
* `Simple_Lowercase_Mapping`, `Simple_Uppercase_Mapping`, and `Simple_Titlecase_Mapping`

To keep the library lightweight, only properties that can be derived exclusively from `UnicodeData.txt` can be supported.

For broader Unicode support, see the [Unicode](https://github.com/xubaiw/Unicode.lean/) library.

## Installation

Add the following dependency to your project's `lakefile.lean`:

```lean
require UnicodeData from git
  "https://github.com/fgdorais/UnicodeData" @ "main"
```

Then add `import UnicodeData` at the top of any lean file where you plan to use this library.

-----

* The UnicodeData library is copyright © 2023 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
* The `UnicodeData.txt` file is copyright © 1991-2023 Unicode, Inc. The file is distributed under the [Unicode® Copyright and Terms of Use](https://www.unicode.org/copyright.html). See the file UNICODE-LICENSE for additional details.
