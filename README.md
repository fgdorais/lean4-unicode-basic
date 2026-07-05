# Lean 4 / Unicode Basic

Basic Unicode support for Lean 4.

Unicode properties that are currently supported by `UnicodeBasic` include:

* `Alphabetic`
* `Bidi_Class`
* `Bidi_Control`
* `Bidi_Paired_Bracket`
* `Bidi_Paired_Bracket_Type`
* `Bidi_Mirrored`
* `Bidi_Mirroring_Glyph`
* `Canonical_Combining_Class`
* `Case_Folding`
* `Case_Ignorable`
* `Cased`
* `Dash`
* `Decomposition_Mapping`
* `Decomposition_Type`
* `Default_Ignorable_Code_Point`
* `Diacritic`
* `East_Asian_Width`
* `Emoji_Component`
* `Emoji_Modifier_Base`
* `Emoji_Modifier`
* `Emoji_Presentation`
* `Emoji`
* `Extended_Pictographic`
* `Extender`
* `Block`
* `General_Category`
* `Grapheme_Base`
* `Grapheme_Cluster_Break`
* `Grapheme_Extend`
* `Hex_Digit`
* `Hyphen`
* `ID_Continue`
* `ID_Start`
* `Line_Break`
* `Lowercase`
* `Math`
* `Name`
* `Noncharacter_Code_Point`
* `Numeric_Type`
* `Numeric_Value`
* `Pattern_Syntax`
* `Pattern_White_Space`
* `Quotation_Mark`
* `Regional_Indicator`
* `Script_Extensions`
* `Script`
* `Sentence_Break`
* `Sentence_Terminal`
* `Simple_Case_Folding`
* `Simple_Lowercase_Mapping`
* `Simple_Titlecase_Mapping`
* `Simple_Uppercase_Mapping`
* `Terminal_Punctuation`
* `Uppercase`
* `White_Space`
* `Word_Break`
* `XID_Continue`
* `XID_Start`
* `Vertical_Orientation`

To keep the `UnicodeBasic` library lightweight, only commonly used properties can be supported. If you need a property not yet in the list above, please submit a feature request!

## Installation

Add the following dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "UnicodeBasic"
git = "https://github.com/fgdorais/lean4-unicode-basic.git"
rev = "main" # or any specific revision
subDir = "lib"
```

Or this dependency to your project's `lakefile.lean`:

```lean4
require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic.git" @ "main" / "lib"
```

Then add `import UnicodeBasic` at the top of any Lean file where you plan to use this library.

## Usage

The main entry point is the root file `UnicodeBasic`. This file contains a description of the main API as well as all primary library functions. The file `UnicodeBasic.Types` contains all the primary data types used in the library.

The remaining files are implementation details. Some of these may be of interest for developers. For example `UnicodeBasic.CharacterDatabase` defines a stream type for parsing files from the [Unicode Character Database](https://www.unicode.org/Public/UCD/latest/ucd/).

## Documentation

Current documentation can be found at [www.dorais.org/lean4-unicode-basic/doc](https://www.dorais.org/lean4-unicode-basic/doc/).
Documentation is also provided for each release since version 1.1.0.

Users can also generate documentation locally using `lake build UnicodeBasic:docs UnicodeData:docs` in the `docs` directory.

-----

* The `Lean 4 / Unicode Basic` library is copyright © 2023-2025 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
* The `UnicodeData.txt` and `PropList.txt` files are copyright © 1991-2025 Unicode®, Inc. The files are distributed under the [Unicode® Copyright and Terms of Use](https://www.unicode.org/copyright.html). See the file LICENSE-UNICODE for additional details.
