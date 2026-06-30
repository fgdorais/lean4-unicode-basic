# UCD TXT Usage

Generated from a repo scan of `data/ucd/**/*.txt` against Lean library files in `UnicodeBasic/` and `UnicodeData/`.

## Summary

- Total txt files: 69
- Used by Lean library: 29
- Unused: 40

## auxiliary

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/auxiliary/GraphemeBreakProperty.txt` | used | UnicodeData/BreakProperties.lean:19 [direct], UnicodeData/BreakProperties.lean:20 [direct], UnicodeData/BreakProperties.lean:31 [direct], UnicodeData/BreakProperties.lean:37 [direct] (4 matches) |
| `data/ucd/auxiliary/GraphemeBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/LineBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/SentenceBreakProperty.txt` | used | UnicodeData/BreakProperties.lean:23 [direct], UnicodeData/BreakProperties.lean:24 [direct], UnicodeData/BreakProperties.lean:49 [direct], UnicodeData/BreakProperties.lean:55 [direct] (4 matches) |
| `data/ucd/auxiliary/SentenceBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/WordBreakProperty.txt` | used | UnicodeBasic.lean:848 [direct], UnicodeData/BreakProperties.lean:21 [direct], UnicodeData/BreakProperties.lean:22 [direct], UnicodeData/BreakProperties.lean:40 [direct], ... (5 matches) |
| `data/ucd/auxiliary/WordBreakTest.txt` | unused |  |

## conformance

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/conformance/BidiCharacterTest.txt` | unused |  |
| `data/ucd/conformance/BidiTest.txt` | unused |  |
| `data/ucd/conformance/NormalizationTest.txt` | unused |  |

## core

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/core/ArabicShaping.txt` | unused |  |
| `data/ucd/core/BidiBrackets.txt` | used | UnicodeData/BidiBrackets.lean:11 [direct], UnicodeData/BidiBrackets.lean:17 [direct], UnicodeData/BidiBrackets.lean:18 [direct], UnicodeData/BidiBrackets.lean:31 [direct] (4 matches) |
| `data/ucd/core/BidiMirroring.txt` | used | UnicodeData/BidiMirroring.lean:12 [direct], UnicodeData/BidiMirroring.lean:13 [direct], UnicodeData/BidiMirroring.lean:15 [direct], UnicodeData/BidiMirroring.lean:17 [direct] (4 matches) |
| `data/ucd/core/Blocks.txt` | used | UnicodeData/Blocks.lean:11 [direct], UnicodeData/Blocks.lean:12 [direct], UnicodeData/Blocks.lean:25 [direct], UnicodeData/Blocks.lean:31 [direct] (4 matches) |
| `data/ucd/core/CaseFolding.txt` | used | UnicodeData/CaseFolding.lean:18 [direct], UnicodeData/CaseFolding.lean:19 [direct], UnicodeData/CaseFolding.lean:22 [direct] (3 matches) |
| `data/ucd/core/CJKRadicals.txt` | unused |  |
| `data/ucd/core/CompositionExclusions.txt` | unused |  |
| `data/ucd/core/DerivedAge.txt` | used | UnicodeData/DerivedAge.lean:11 [direct], UnicodeData/DerivedAge.lean:12 [direct], UnicodeData/DerivedAge.lean:29 [direct], UnicodeData/DerivedAge.lean:31 [direct], ... (6 matches) |
| `data/ucd/core/DerivedCoreProperties.txt` | used | UnicodeData/DerivedCoreProperties.lean:11 [direct], UnicodeData/DerivedCoreProperties.lean:28 [direct], UnicodeData/DerivedCoreProperties.lean:29 [direct], UnicodeData/DerivedCoreProperties.lean:32 [direct], ... (5 matches) |
| `data/ucd/core/DerivedNormalizationProps.txt` | unused |  |
| `data/ucd/core/DoNotEmit.txt` | unused |  |
| `data/ucd/core/EastAsianWidth.txt` | used | UnicodeData/EastAsianWidth.lean:11 [direct], UnicodeData/EastAsianWidth.lean:12 [direct], UnicodeData/EastAsianWidth.lean:14 [direct], UnicodeData/EastAsianWidth.lean:16 [direct], ... (5 matches) |
| `data/ucd/core/EmojiSources.txt` | unused |  |
| `data/ucd/core/EquivalentUnifiedIdeograph.txt` | unused |  |
| `data/ucd/core/HangulSyllableType.txt` | unused |  |
| `data/ucd/core/IndicPositionalCategory.txt` | unused |  |
| `data/ucd/core/IndicSyllabicCategory.txt` | unused |  |
| `data/ucd/core/Jamo.txt` | unused |  |
| `data/ucd/core/LineBreak.txt` | used | UnicodeData/BreakProperties.lean:25 [direct], UnicodeData/BreakProperties.lean:26 [direct], UnicodeData/BreakProperties.lean:58 [direct], UnicodeData/BreakProperties.lean:64 [direct], ... (10 matches) |
| `data/ucd/core/NameAliases.txt` | unused |  |
| `data/ucd/core/NamedSequences.txt` | unused |  |
| `data/ucd/core/NamedSequencesProv.txt` | unused |  |
| `data/ucd/core/NamesList.txt` | unused |  |
| `data/ucd/core/NormalizationCorrections.txt` | unused |  |
| `data/ucd/core/NushuSources.txt` | unused |  |
| `data/ucd/core/PropertyAliases.txt` | used | UnicodeData/Aliases.lean:18 [direct], UnicodeData/Aliases.lean:19 [direct], UnicodeData/Aliases.lean:22 [direct] (3 matches) |
| `data/ucd/core/PropertyValueAliases.txt` | used | UnicodeData/Aliases.lean:63 [direct], UnicodeData/Aliases.lean:66 [direct] (2 matches) |
| `data/ucd/core/PropList.txt` | used | UnicodeBasic.lean:527 [direct], UnicodeBasic.lean:1071 [direct], UnicodeData/PropList.lean:11 [direct], UnicodeData/PropList.lean:58 [direct], ... (23 matches) |
| `data/ucd/core/ScriptExtensions.txt` | used | UnicodeData/ScriptExtensions.lean:15 [direct], UnicodeData/ScriptExtensions.lean:16 [direct], UnicodeData/ScriptExtensions.lean:19 [direct], UnicodeData/ScriptExtensions.lean:26 [direct] (4 matches) |
| `data/ucd/core/Scripts.txt` | used | UnicodeData/Scripts.lean:15 [direct], UnicodeData/Scripts.lean:16 [direct], UnicodeData/Scripts.lean:19 [direct], UnicodeData/Scripts.lean:26 [direct] (4 matches) |
| `data/ucd/core/SpecialCasing.txt` | unused |  |
| `data/ucd/core/StandardizedVariants.txt` | unused |  |
| `data/ucd/core/TangutSources.txt` | unused |  |
| `data/ucd/core/UnicodeData.txt` | used | UnicodeData/Basic.lean:13 [direct], UnicodeData/Basic.lean:115 [direct], UnicodeData/Basic.lean:116 [direct], UnicodeData/Basic.lean:118 [direct], ... (11 matches) |
| `data/ucd/core/Unikemet.txt` | unused |  |
| `data/ucd/core/USourceData.txt` | unused |  |
| `data/ucd/core/VerticalOrientation.txt` | used | UnicodeData/VerticalOrientation.lean:11 [direct], UnicodeData/VerticalOrientation.lean:12 [direct], UnicodeData/VerticalOrientation.lean:14 [direct], UnicodeData/VerticalOrientation.lean:16 [direct], ... (5 matches) |

## emoji

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/emoji/emoji-data.txt` | used | UnicodeData/Emoji.lean:11 [direct], UnicodeData/Emoji.lean:21 [direct], UnicodeData/Emoji.lean:22 [direct], UnicodeData/Emoji.lean:32 [direct] (4 matches) |
| `data/ucd/emoji/emoji-variation-sequences.txt` | unused |  |

## extracted

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/extracted/DerivedBidiClass.txt` | used | UnicodeData/DerivedBidiClass.lean:11 [direct], UnicodeData/DerivedBidiClass.lean:12 [direct], UnicodeData/DerivedBidiClass.lean:29 [direct], UnicodeData/DerivedBidiClass.lean:38 [direct], ... (6 matches) |
| `data/ucd/extracted/DerivedBinaryProperties.txt` | used | UnicodeData/DerivedBinaryProperties.lean:11 [direct], UnicodeData/DerivedBinaryProperties.lean:12 [direct], UnicodeData/DerivedBinaryProperties.lean:17 [direct], UnicodeData/DerivedBinaryProperties.lean:23 [direct] (4 matches) |
| `data/ucd/extracted/DerivedCombiningClass.txt` | used | UnicodeData/DerivedCombiningClass.lean:11 [direct], UnicodeData/DerivedCombiningClass.lean:12 [direct], UnicodeData/DerivedCombiningClass.lean:17 [direct], UnicodeData/DerivedCombiningClass.lean:23 [direct] (4 matches) |
| `data/ucd/extracted/DerivedDecompositionType.txt` | used | UnicodeData/DerivedDecompositionType.lean:11 [direct], UnicodeData/DerivedDecompositionType.lean:12 [direct], UnicodeData/DerivedDecompositionType.lean:17 [direct], UnicodeData/DerivedDecompositionType.lean:23 [direct] (4 matches) |
| `data/ucd/extracted/DerivedEastAsianWidth.txt` | used | UnicodeData/EastAsianWidth.lean:11 [direct], UnicodeData/EastAsianWidth.lean:12 [direct] (2 matches) |
| `data/ucd/extracted/DerivedGeneralCategory.txt` | used | UnicodeData/DerivedGeneralCategory.lean:11 [direct], UnicodeData/DerivedGeneralCategory.lean:12 [direct], UnicodeData/DerivedGeneralCategory.lean:14 [direct], UnicodeData/DerivedGeneralCategory.lean:17 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedJoiningGroup.txt` | used | UnicodeData/DerivedJoiningGroup.lean:11 [direct], UnicodeData/DerivedJoiningGroup.lean:12 [direct], UnicodeData/DerivedJoiningGroup.lean:29 [direct], UnicodeData/DerivedJoiningGroup.lean:35 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedJoiningType.txt` | unused |  |
| `data/ucd/extracted/DerivedLineBreak.txt` | used | UnicodeData/DerivedLineBreak.lean:12 [direct], UnicodeData/DerivedLineBreak.lean:13 [direct], UnicodeData/DerivedLineBreak.lean:30 [direct], UnicodeData/DerivedLineBreak.lean:39 [direct], ... (6 matches) |
| `data/ucd/extracted/DerivedName.txt` | unused |  |
| `data/ucd/extracted/DerivedNumericType.txt` | used | UnicodeData/DerivedNumericType.lean:11 [direct], UnicodeData/DerivedNumericType.lean:12 [direct], UnicodeData/DerivedNumericType.lean:17 [direct], UnicodeData/DerivedNumericType.lean:23 [direct] (4 matches) |
| `data/ucd/extracted/DerivedNumericValues.txt` | used | UnicodeData/DerivedNumericValues.lean:12 [direct], UnicodeData/DerivedNumericValues.lean:13 [direct], UnicodeData/DerivedNumericValues.lean:30 [direct], UnicodeData/DerivedNumericValues.lean:42 [direct], ... (5 matches) |

## unihan

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/unihan/Unihan_DictionaryIndices.txt` | unused |  |
| `data/ucd/unihan/Unihan_DictionaryLikeData.txt` | unused |  |
| `data/ucd/unihan/Unihan_IRGSources.txt` | unused |  |
| `data/ucd/unihan/Unihan_NumericValues.txt` | unused |  |
| `data/ucd/unihan/Unihan_OtherMappings.txt` | unused |  |
| `data/ucd/unihan/Unihan_RadicalStrokeCounts.txt` | unused |  |
| `data/ucd/unihan/Unihan_Readings.txt` | unused |  |
| `data/ucd/unihan/Unihan_Variants.txt` | unused |  |

