# Data Table Provenance

Generated from `makeTables.lean`.

## Used To Construct `data/table`

| data/table file | generator | UCD sources |
| --- | --- | --- |
| `data/table/Alphabetic.txt` | `mkAlphabetic` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Bidi_Brackets.txt` | `mkBidiBrackets` | `data/ucd/core/BidiBrackets.txt` |
| `data/table/Bidi_Class.txt` | `mkBidiClass` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Bidi_Mirrored.txt` | `mkBidiMirrored` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Bidi_Mirroring_Glyph.txt` | `mkBidiMirroringGlyph` | `data/ucd/core/BidiMirroring.txt` |
| `data/table/Block_Name.txt` | `mkBlockName` | `data/ucd/core/Blocks.txt` |
| `data/table/Canonical_Combining_Class.txt` | `mkCanonicalCombiningClass` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Canonical_Decomposition_Mapping.txt` | `mkCanonicalDecompositionMapping` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Case_Folding.txt` | `mkCaseFolding` | `data/ucd/core/CaseFolding.txt` |
| `data/table/Case_Mapping.txt` | `mkCaseMapping` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Cased.txt` | `mkCased` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Dash.txt` | `mkDash` | `data/ucd/core/PropList.txt` |
| `data/table/Decomposition_Mapping.txt` | `mkDecompositionMapping` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Default_Ignorable_Code_Point.txt` | `mkDefaultIgnorableCodePoint` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Diacritic.txt` | `mkDiacritic` | `data/ucd/core/PropList.txt` |
| `data/table/East_Asian_Width.txt` | `mkEastAsianWidth` | `data/ucd/extracted/DerivedEastAsianWidth.txt` |
| `data/table/Emoji.txt` | `mkEmoji` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Emoji_Component.txt` | `mkEmojiComponent` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Emoji_Modifier.txt` | `mkEmojiModifier` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Emoji_Modifier_Base.txt` | `mkEmojiModifierBase` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Emoji_Presentation.txt` | `mkEmojiPresentation` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Extended_Pictographic.txt` | `mkExtendedPictographic` | `data/ucd/emoji/emoji-data.txt` |
| `data/table/Extender.txt` | `mkExtender` | `data/ucd/core/PropList.txt` |
| `data/table/General_Category.txt` | `mkGC` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Grapheme_Base.txt` | `mkGraphemeBase` | `data/ucd/core/DerivedCoreProperties.txt` |
| `data/table/Grapheme_Break.txt` | `mkGraphemeBreak` | `data/ucd/auxiliary/GraphemeBreakProperty.txt` |
| `data/table/Grapheme_Extend.txt` | `mkGraphemeExtend` | `data/ucd/core/DerivedCoreProperties.txt` |
| `data/table/Hyphen.txt` | `mkHyphen` | `data/ucd/core/PropList.txt` |
| `data/table/ID_Continue.txt` | `mkIDContinue` | `data/ucd/core/DerivedCoreProperties.txt` |
| `data/table/ID_Start.txt` | `mkIDStart` | `data/ucd/core/DerivedCoreProperties.txt` |
| `data/table/Line_Break.txt` | `mkLineBreak` | `data/ucd/core/LineBreak.txt` |
| `data/table/Lowercase.txt` | `mkLowercase` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Math.txt` | `mkMath` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Name.txt` | `mkName` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Noncharacter_Code_Point.txt` | `mkNoncharacterCodePoint` | `data/ucd/core/PropList.txt` |
| `data/table/Numeric_Value.txt` | `mkNumericValue` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Other.txt` | `mkOther` | `data/ucd/core/PropList.txt` |
| `data/table/Other_Alphabetic.txt` | `mkOtherAlphabetic` | `data/ucd/core/PropList.txt` |
| `data/table/Other_Default_Ignorable_Code_Point.txt` | `mkOtherDefaultIgnorableCodePoint` | `data/ucd/core/PropList.txt` |
| `data/table/Other_Lowercase.txt` | `mkOtherLowercase` | `data/ucd/core/PropList.txt` |
| `data/table/Other_Math.txt` | `mkOtherMath` | `data/ucd/core/PropList.txt` |
| `data/table/Other_Uppercase.txt` | `mkOtherUppercase` | `data/ucd/core/PropList.txt` |
| `data/table/Pattern_Syntax.txt` | `mkPatternSyntax` | `data/ucd/core/PropList.txt` |
| `data/table/Pattern_White_Space.txt` | `mkPatternWhiteSpace` | `data/ucd/core/PropList.txt` |
| `data/table/Prepended_Concatenation_Mark.txt` | `mkPrependedConcatenationMark` | `data/ucd/core/PropList.txt` |
| `data/table/Quotation_Mark.txt` | `mkQuotationMark` | `data/ucd/core/PropList.txt` |
| `data/table/Regional_Indicator.txt` | `mkRegionalIndicator` | `data/ucd/core/PropList.txt` |
| `data/table/Script_Extensions.txt` | `mkScriptExtensions` | `data/ucd/core/ScriptExtensions.txt` |
| `data/table/Script_Name.txt` | `mkScriptName` | `data/ucd/core/PropertyValueAliases.txt` |
| `data/table/Sentence_Break.txt` | `mkSentenceBreak` | `data/ucd/auxiliary/SentenceBreakProperty.txt` |
| `data/table/Sentence_Terminal.txt` | `mkSentenceTerminal` | `data/ucd/core/PropList.txt` |
| `data/table/Simple_Case_Folding.txt` | `mkSimpleCaseFolding` | `data/ucd/core/CaseFolding.txt` |
| `data/table/Terminal_Punctuation.txt` | `mkTerminalPunctuation` | `data/ucd/core/PropList.txt` |
| `data/table/Titlecase.txt` | `mkTitlecase` | `data/ucd/core/UnicodeData.txt` |
| `data/table/Uppercase.txt` | `mkUppercase` | `data/ucd/core/PropList.txt`, `data/ucd/core/UnicodeData.txt` |
| `data/table/Variation_Selector.txt` | `mkVariationSelector` | `data/ucd/core/PropList.txt` |
| `data/table/Vertical_Orientation.txt` | `mkVerticalOrientation` | `data/ucd/core/VerticalOrientation.txt` |
| `data/table/White_Space.txt` | `mkWhiteSpace` | `data/ucd/core/PropList.txt` |
| `data/table/Word_Break.txt` | `mkWordBreak` | `data/ucd/auxiliary/WordBreakProperty.txt` |
| `data/table/XID_Continue.txt` | `mkXIDContinue` | `data/ucd/core/DerivedCoreProperties.txt` |
| `data/table/XID_Start.txt` | `mkXIDStart` | `data/ucd/core/DerivedCoreProperties.txt` |

## Not Used To Construct `data/table`

These UCD text files are present in the repository but are not referenced by `makeTables.lean`.

### auxiliary

- `data/ucd/auxiliary/GraphemeBreakTest.txt`
- `data/ucd/auxiliary/LineBreakTest.txt`
- `data/ucd/auxiliary/SentenceBreakTest.txt`
- `data/ucd/auxiliary/WordBreakTest.txt`

### conformance

- `data/ucd/conformance/BidiCharacterTest.txt`
- `data/ucd/conformance/BidiTest.txt`
- `data/ucd/conformance/NormalizationTest.txt`

### core

- `data/ucd/core/ArabicShaping.txt`
- `data/ucd/core/CJKRadicals.txt`
- `data/ucd/core/CompositionExclusions.txt`
- `data/ucd/core/DerivedAge.txt`
- `data/ucd/core/DerivedNormalizationProps.txt`
- `data/ucd/core/DoNotEmit.txt`
- `data/ucd/core/EastAsianWidth.txt`
- `data/ucd/core/EmojiSources.txt`
- `data/ucd/core/EquivalentUnifiedIdeograph.txt`
- `data/ucd/core/HangulSyllableType.txt`
- `data/ucd/core/IndicPositionalCategory.txt`
- `data/ucd/core/IndicSyllabicCategory.txt`
- `data/ucd/core/Jamo.txt`
- `data/ucd/core/NameAliases.txt`
- `data/ucd/core/NamedSequences.txt`
- `data/ucd/core/NamedSequencesProv.txt`
- `data/ucd/core/NamesList.txt`
- `data/ucd/core/NormalizationCorrections.txt`
- `data/ucd/core/NushuSources.txt`
- `data/ucd/core/PropertyAliases.txt`
- `data/ucd/core/Scripts.txt`
- `data/ucd/core/SpecialCasing.txt`
- `data/ucd/core/StandardizedVariants.txt`
- `data/ucd/core/TangutSources.txt`
- `data/ucd/core/Unikemet.txt`
- `data/ucd/core/USourceData.txt`

### emoji

- `data/ucd/emoji/emoji-variation-sequences.txt`

### extracted

- `data/ucd/extracted/DerivedBidiClass.txt`
- `data/ucd/extracted/DerivedBinaryProperties.txt`
- `data/ucd/extracted/DerivedCombiningClass.txt`
- `data/ucd/extracted/DerivedDecompositionType.txt`
- `data/ucd/extracted/DerivedGeneralCategory.txt`
- `data/ucd/extracted/DerivedJoiningGroup.txt`
- `data/ucd/extracted/DerivedJoiningType.txt`
- `data/ucd/extracted/DerivedLineBreak.txt`
- `data/ucd/extracted/DerivedName.txt`
- `data/ucd/extracted/DerivedNumericType.txt`
- `data/ucd/extracted/DerivedNumericValues.txt`

### unihan

- `data/ucd/unihan/Unihan_DictionaryIndices.txt`
- `data/ucd/unihan/Unihan_DictionaryLikeData.txt`
- `data/ucd/unihan/Unihan_IRGSources.txt`
- `data/ucd/unihan/Unihan_NumericValues.txt`
- `data/ucd/unihan/Unihan_OtherMappings.txt`
- `data/ucd/unihan/Unihan_RadicalStrokeCounts.txt`
- `data/ucd/unihan/Unihan_Readings.txt`
- `data/ucd/unihan/Unihan_Variants.txt`

