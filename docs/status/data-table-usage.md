# Data Table Usage

Generated from `UnicodeBasic/TableLookup.lean`.

## Directly Read By `UnicodeBasic.TableLookup`

| data/table file | lookup | path |
| --- | --- | --- |
| `data/table/Bidi_Brackets.txt` | `lookupBidiBracket` | Lean reads `data/table/Bidi_Brackets.txt` with `include_str` |
| `data/table/Bidi_Mirroring_Glyph.txt` | `lookupBidiMirroringGlyph` | Lean reads `data/table/Bidi_Mirroring_Glyph.txt` with `include_str` |
| `data/table/Block_Name.txt` | `lookupBlockName` | Lean reads `data/table/Block_Name.txt` with `include_str` |
| `data/table/Canonical_Decomposition_Mapping.txt` | `lookupCanonicalDecompositionMapping` | Lean reads `data/table/Canonical_Decomposition_Mapping.txt` with `include_str` |
| `data/table/Case_Folding.txt` | `lookupCaseFolding` | Lean reads `data/table/Case_Folding.txt` with `include_str` |
| `data/table/Dash.txt` | `lookupDash` | Lean reads `data/table/Dash.txt` with `include_str` |
| `data/table/Decomposition_Mapping.txt` | `lookupDecompositionMapping` | Lean reads `data/table/Decomposition_Mapping.txt` with `include_str` |
| `data/table/Default_Ignorable_Code_Point.txt` | `lookupDefaultIgnorableCodePoint` | Lean reads `data/table/Default_Ignorable_Code_Point.txt` with `include_str` |
| `data/table/Diacritic.txt` | `lookupDiacritic` | Lean reads `data/table/Diacritic.txt` with `include_str` |
| `data/table/East_Asian_Width.txt` | `lookupEastAsianWidth` | Lean reads `data/table/East_Asian_Width.txt` with `include_str` |
| `data/table/Emoji_Component.txt` | `lookupEmojiComponent` | Lean reads `data/table/Emoji_Component.txt` with `include_str` |
| `data/table/Emoji_Modifier_Base.txt` | `lookupEmojiModifierBase` | Lean reads `data/table/Emoji_Modifier_Base.txt` with `include_str` |
| `data/table/Emoji_Modifier.txt` | `lookupEmojiModifier` | Lean reads `data/table/Emoji_Modifier.txt` with `include_str` |
| `data/table/Emoji_Presentation.txt` | `lookupEmojiPresentation` | Lean reads `data/table/Emoji_Presentation.txt` with `include_str` |
| `data/table/Emoji.txt` | `lookupEmoji` | Lean reads `data/table/Emoji.txt` with `include_str` |
| `data/table/Extended_Pictographic.txt` | `lookupExtendedPictographic` | Lean reads `data/table/Extended_Pictographic.txt` with `include_str` |
| `data/table/Extender.txt` | `lookupExtender` | Lean reads `data/table/Extender.txt` with `include_str` |
| `data/table/Grapheme_Base.txt` | `lookupGraphemeBase` | Lean reads `data/table/Grapheme_Base.txt` with `include_str` |
| `data/table/Grapheme_Break.txt` | `lookupGraphemeClusterBreak` | Lean reads `data/table/Grapheme_Break.txt` with `include_str` |
| `data/table/Grapheme_Extend.txt` | `lookupGraphemeExtend` | Lean reads `data/table/Grapheme_Extend.txt` with `include_str` |
| `data/table/Hyphen.txt` | `lookupHyphen` | Lean reads `data/table/Hyphen.txt` with `include_str` |
| `data/table/ID_Continue.txt` | `lookupIDContinue` | Lean reads `data/table/ID_Continue.txt` with `include_str` |
| `data/table/ID_Start.txt` | `lookupIDStart` | Lean reads `data/table/ID_Start.txt` with `include_str` |
| `data/table/Name.txt` | `lookupName` | Lean reads `data/table/Name.txt` with `include_str` |
| `data/table/Pattern_Syntax.txt` | `lookupPatternSyntax` | Lean reads `data/table/Pattern_Syntax.txt` with `include_str` |
| `data/table/Pattern_White_Space.txt` | `lookupPatternWhiteSpace` | Lean reads `data/table/Pattern_White_Space.txt` with `include_str` |
| `data/table/Quotation_Mark.txt` | `lookupQuotationMark` | Lean reads `data/table/Quotation_Mark.txt` with `include_str` |
| `data/table/Regional_Indicator.txt` | `lookupRegionalIndicator` | Lean reads `data/table/Regional_Indicator.txt` with `include_str` |
| `data/table/Script_Extensions.txt` | `lookupScriptExtensions` | Lean reads `data/table/Script_Extensions.txt` with `include_str` |
| `data/table/Script_Name.txt` | `lookupScriptName` | Lean reads `data/table/Script_Name.txt` with `include_str` |
| `data/table/Sentence_Break.txt` | `lookupSentenceBreak` | Lean reads `data/table/Sentence_Break.txt` with `include_str` |
| `data/table/Sentence_Terminal.txt` | `lookupSentenceTerminal` | Lean reads `data/table/Sentence_Terminal.txt` with `include_str` |
| `data/table/Simple_Case_Folding.txt` | `lookupSimpleCaseFolding` | Lean reads `data/table/Simple_Case_Folding.txt` with `include_str` |
| `data/table/Terminal_Punctuation.txt` | `lookupTerminalPunctuation` | Lean reads `data/table/Terminal_Punctuation.txt` with `include_str` |
| `data/table/Vertical_Orientation.txt` | `lookupVerticalOrientation` | Lean reads `data/table/Vertical_Orientation.txt` with `include_str` |
| `data/table/White_Space.txt` | `lookupWhiteSpace` | Lean reads `data/table/White_Space.txt` with `include_str` |
| `data/table/Word_Break.txt` | `lookupWordBreak` | Lean reads `data/table/Word_Break.txt` with `include_str` |
| `data/table/XID_Continue.txt` | `lookupXIDContinue` | Lean reads `data/table/XID_Continue.txt` with `include_str` |
| `data/table/XID_Start.txt` | `lookupXIDStart` | Lean reads `data/table/XID_Start.txt` with `include_str` |

## Backed By `UnicodeCLib`

These lookups are exposed from Lean through externs in `UnicodeBasic.TableLookup`, but the implementation lives in generated C code under `UnicodeCLib/`.

| lookup | backend | note |
| --- | --- | --- |
| `lookupAlphabetic` | `UnicodeCLib.lookupProp` | Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Alphabetic.txt` file is not read directly by Lean. |
| `lookupCaseMapping` | `UnicodeCLib.lookupCase` | Uses the packed case-mapping table produced by `UnicodeCLib/case.c`; the generated `data/table/Case_Mapping.txt` file is not read directly by Lean. |
| `lookupCased` | `UnicodeCLib.lookupProp` | Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Cased.txt` file is not read directly by Lean. |
| `lookupLowercase` | `UnicodeCLib.lookupProp` | Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Lowercase.txt` file is not read directly by Lean. |
| `lookupMath` | `UnicodeCLib.lookupProp` | Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Math.txt` file is not read directly by Lean. |
| `lookupOther` | `UnicodeCLib.lookupProp` | Extracts the auxiliary property bits from `UnicodeCLib/prop.c`; the generated `data/table/Other*.txt` files are not read directly by Lean. |
| `lookupScript` | `UnicodeCLib.lookupScript` | Uses the script table produced by `UnicodeCLib/script.c`; no `data/table` file is read for this lookup. |
| `lookupUppercase` | `UnicodeCLib.lookupProp` | Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Uppercase.txt` file is not read directly by Lean. |

## Backed By `UnicodeData`

These lookups are implemented from `UnicodeData` modules rather than by reading a `data/table/*.txt` file in Lean.

| lookup | backend | note |
| --- | --- | --- |
| `lookupBidiClass` | `UnicodeData.Extracted.DerivedBidiClass` | The lookup is implemented from `UnicodeData.Extracted.DerivedBidiClass`; the generated `data/table/Bidi_Class.txt` file is not read directly by Lean. |
| `lookupBidiMirrored` | `UnicodeData.Extracted.DerivedBinaryProperties` | The lookup is implemented from `UnicodeData.Extracted.DerivedBinaryProperties`; the generated `data/table/Bidi_Mirrored.txt` file is not read directly by Lean. |
| `lookupCanonicalCombiningClass` | `UnicodeData.Extracted.DerivedCombiningClass` | The lookup is implemented from `UnicodeData.Extracted.DerivedCombiningClass`; the generated `data/table/Canonical_Combining_Class.txt` file is not read directly by Lean. |
| `lookupGC` | `UnicodeData.Extracted.DerivedGeneralCategory` | The lookup is implemented from `UnicodeData.Extracted.DerivedGeneralCategory`; the generated `data/table/General_Category.txt` file is not read directly by Lean. |
| `lookupLineBreak` | `UnicodeData.Extracted.DerivedLineBreak` | The lookup is implemented from `UnicodeData.Extracted.DerivedLineBreak`; the generated `data/table/Line_Break.txt` file is not read directly by Lean. |
| `lookupNumericValue` | `UnicodeData.Basic + UnicodeData.Extracted.DerivedNumericValues` | The lookup is assembled from `UnicodeData.Basic` and `UnicodeData.Extracted.DerivedNumericValues`; the generated `data/table/Numeric_Value.txt` file is not read directly by Lean. |
| `lookupTitlecase` | `UnicodeBasic.TableLookup.lookupGC` | This lookup is derived from `lookupGC`; the generated `data/table/Titlecase.txt` file is not read directly by Lean. |

## Generated But Not Directly Read By `UnicodeBasic.TableLookup`

These tables are generated by `makeTables.lean`, but current Lean code does not `include_str` them directly.

### Alphabetic.txt

- `data/table/Alphabetic.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupAlphabetic`.

### Bidi_Class.txt

- `data/table/Bidi_Class.txt` - Equivalent lookup is provided by `UnicodeData.Extracted.DerivedBidiClass` via `lookupBidiClass`.

### Bidi_Mirrored.txt

- `data/table/Bidi_Mirrored.txt` - Equivalent lookup is provided by `UnicodeData.Extracted.DerivedBinaryProperties` via `lookupBidiMirrored`.

### Canonical_Combining_Class.txt

- `data/table/Canonical_Combining_Class.txt` - Equivalent lookup is provided by `UnicodeData.Extracted.DerivedCombiningClass` via `lookupCanonicalCombiningClass`.

### Case_Mapping.txt

- `data/table/Case_Mapping.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupCase` via `lookupCaseMapping`.

### Cased.txt

- `data/table/Cased.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupCased`.

### General_Category.txt

- `data/table/General_Category.txt` - Equivalent lookup is provided by `UnicodeData.Extracted.DerivedGeneralCategory` via `lookupGC`.

### Line_Break.txt

- `data/table/Line_Break.txt` - Equivalent lookup is provided by `UnicodeData.Extracted.DerivedLineBreak` via `lookupLineBreak`.

### Lowercase.txt

- `data/table/Lowercase.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupLowercase`.

### Math.txt

- `data/table/Math.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupMath`.

### Noncharacter_Code_Point.txt

- `data/table/Noncharacter_Code_Point.txt` - This is computed directly in Lean by a range check; the generated table is not read directly.

### Numeric_Value.txt

- `data/table/Numeric_Value.txt` - Equivalent lookup is assembled from `UnicodeData.Basic` and `UnicodeData.Extracted.DerivedNumericValues` via `lookupNumericValue`.

### Other.txt

- `data/table/Other.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupOther`.

### Other_Alphabetic.txt

- `data/table/Other_Alphabetic.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupAlphabetic`.

### Other_Default_Ignorable_Code_Point.txt

- `data/table/Other_Default_Ignorable_Code_Point.txt` - No current `UnicodeBasic.TableLookup` consumer reads this table directly.

### Other_Lowercase.txt

- `data/table/Other_Lowercase.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupLowercase`.

### Other_Math.txt

- `data/table/Other_Math.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupMath`.

### Other_Uppercase.txt

- `data/table/Other_Uppercase.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupUppercase`.

### Prepended_Concatenation_Mark.txt

- `data/table/Prepended_Concatenation_Mark.txt` - This property is only used as an exclusion inside `lookupDefaultIgnorableCodePoint`; the generated table is not read directly.

### Titlecase.txt

- `data/table/Titlecase.txt` - Equivalent lookup is derived from `lookupGC` via `lookupTitlecase`.

### Uppercase.txt

- `data/table/Uppercase.txt` - Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupUppercase`.

### Variation_Selector.txt

- `data/table/Variation_Selector.txt` - This property is only used as part of the `lookupDefaultIgnorableCodePoint` logic; the generated table is not read directly.

