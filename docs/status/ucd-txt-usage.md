# UCD TXT Usage

Generated from a repo scan of `data/ucd/**/*.txt` against Lean library files in `UnicodeBasic/` and `UnicodeData/`.

## Skipped

These files are part of the UCD distribution but are intentionally excluded from Lean usage counts because they are not machine-readable property tables.

| File | Reason |
| --- | --- |
| `data/ucd/core/DoNotEmit.txt` | editorial prose file with no machine-readable record schema |
| `data/ucd/core/NamesList.txt` | semi-structured reference text explicitly not intended for machine parsing |

## Summary

- Total txt files: 67
- Used by Lean library: 60
- Unused: 7

## auxiliary

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/auxiliary/GraphemeBreakProperty.txt` | used | UnicodeData/Auxiliary/BreakProperties.lean:19 [direct], UnicodeData/Auxiliary/BreakProperties.lean:20 [direct], UnicodeData/Auxiliary/BreakProperties.lean:31 [direct], UnicodeData/Auxiliary/BreakProperties.lean:37 [direct] (4 matches) |
| `data/ucd/auxiliary/GraphemeBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/LineBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/SentenceBreakProperty.txt` | used | UnicodeData/Auxiliary/BreakProperties.lean:23 [direct], UnicodeData/Auxiliary/BreakProperties.lean:24 [direct], UnicodeData/Auxiliary/BreakProperties.lean:49 [direct], UnicodeData/Auxiliary/BreakProperties.lean:55 [direct] (4 matches) |
| `data/ucd/auxiliary/SentenceBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/WordBreakProperty.txt` | used | UnicodeBasic.lean:848 [direct], UnicodeData/Auxiliary/BreakProperties.lean:21 [direct], UnicodeData/Auxiliary/BreakProperties.lean:22 [direct], UnicodeData/Auxiliary/BreakProperties.lean:40 [direct], ... (5 matches) |
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
| `data/ucd/core/ArabicShaping.txt` | used | UnicodeData/Core/ArabicShaping.lean:11 [direct], UnicodeData/Core/ArabicShaping.lean:12 [direct], UnicodeData/Core/ArabicShaping.lean:22 [direct], UnicodeData/Core/ArabicShaping.lean:25 [direct] (4 matches) |
| `data/ucd/core/BidiBrackets.txt` | used | UnicodeData/Core/BidiBrackets.lean:11 [direct], UnicodeData/Core/BidiBrackets.lean:17 [direct], UnicodeData/Core/BidiBrackets.lean:18 [direct], UnicodeData/Core/BidiBrackets.lean:31 [direct] (4 matches) |
| `data/ucd/core/BidiMirroring.txt` | used | UnicodeData/Core/BidiMirroring.lean:12 [direct], UnicodeData/Core/BidiMirroring.lean:13 [direct], UnicodeData/Core/BidiMirroring.lean:15 [direct], UnicodeData/Core/BidiMirroring.lean:17 [direct] (4 matches) |
| `data/ucd/core/Blocks.txt` | used | UnicodeData/Core/Blocks.lean:11 [direct], UnicodeData/Core/Blocks.lean:12 [direct], UnicodeData/Core/Blocks.lean:25 [direct], UnicodeData/Core/Blocks.lean:31 [direct] (4 matches) |
| `data/ucd/core/CaseFolding.txt` | used | UnicodeData/Core/CaseFolding.lean:18 [direct], UnicodeData/Core/CaseFolding.lean:19 [direct], UnicodeData/Core/CaseFolding.lean:22 [direct] (3 matches) |
| `data/ucd/core/CJKRadicals.txt` | used | UnicodeData/Core/CJKRadicals.lean:11 [direct], UnicodeData/Core/CJKRadicals.lean:12 [direct], UnicodeData/Core/CJKRadicals.lean:21 [direct], UnicodeData/Core/CJKRadicals.lean:24 [direct] (4 matches) |
| `data/ucd/core/CompositionExclusions.txt` | used | UnicodeData/Core/CompositionExclusions.lean:11 [direct], UnicodeData/Core/CompositionExclusions.lean:12 [direct], UnicodeData/Core/CompositionExclusions.lean:17 [direct] (3 matches) |
| `data/ucd/core/DerivedAge.txt` | used | UnicodeData/Core/DerivedAge.lean:11 [direct], UnicodeData/Core/DerivedAge.lean:12 [direct], UnicodeData/Core/DerivedAge.lean:14 [direct], UnicodeData/Core/DerivedAge.lean:16 [direct], ... (5 matches) |
| `data/ucd/core/DerivedCoreProperties.txt` | used | UnicodeData/Core/DerivedCoreProperties.lean:11 [direct], UnicodeData/Core/DerivedCoreProperties.lean:28 [direct], UnicodeData/Core/DerivedCoreProperties.lean:29 [direct], UnicodeData/Core/DerivedCoreProperties.lean:32 [direct], ... (5 matches) |
| `data/ucd/core/DerivedNormalizationProps.txt` | used | UnicodeData/Core/DerivedNormalizationProps.lean:11 [direct], UnicodeData/Core/DerivedNormalizationProps.lean:12 [direct], UnicodeData/Core/DerivedNormalizationProps.lean:29 [direct], UnicodeData/Core/DerivedNormalizationProps.lean:40 [direct], ... (6 matches) |
| `data/ucd/core/EastAsianWidth.txt` | used | UnicodeData/Extracted/DerivedEastAsianWidth.lean:11 [direct], UnicodeData/Extracted/DerivedEastAsianWidth.lean:12 [direct], UnicodeData/Extracted/DerivedEastAsianWidth.lean:14 [direct], UnicodeData/Extracted/DerivedEastAsianWidth.lean:16 [direct] (4 matches) |
| `data/ucd/core/EmojiSources.txt` | used | UnicodeData/Core/EmojiSources.lean:11 [direct], UnicodeData/Core/EmojiSources.lean:12 [direct], UnicodeData/Core/EmojiSources.lean:22 [direct], UnicodeData/Core/EmojiSources.lean:25 [direct] (4 matches) |
| `data/ucd/core/EquivalentUnifiedIdeograph.txt` | used | UnicodeData/Core/EquivalentUnifiedIdeograph.lean:11 [direct], UnicodeData/Core/EquivalentUnifiedIdeograph.lean:12 [direct], UnicodeData/Core/EquivalentUnifiedIdeograph.lean:21 [direct], UnicodeData/Core/EquivalentUnifiedIdeograph.lean:24 [direct] (4 matches) |
| `data/ucd/core/HangulSyllableType.txt` | used | UnicodeData/Core/HangulSyllableType.lean:11 [direct], UnicodeData/Core/HangulSyllableType.lean:12 [direct], UnicodeData/Core/HangulSyllableType.lean:14 [direct], UnicodeData/Core/HangulSyllableType.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/IndicPositionalCategory.txt` | used | UnicodeData/Core/IndicPositionalCategory.lean:11 [direct], UnicodeData/Core/IndicPositionalCategory.lean:12 [direct], UnicodeData/Core/IndicPositionalCategory.lean:14 [direct], UnicodeData/Core/IndicPositionalCategory.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/IndicSyllabicCategory.txt` | used | UnicodeData/Core/IndicSyllabicCategory.lean:11 [direct], UnicodeData/Core/IndicSyllabicCategory.lean:12 [direct], UnicodeData/Core/IndicSyllabicCategory.lean:14 [direct], UnicodeData/Core/IndicSyllabicCategory.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/Jamo.txt` | used | UnicodeData/Core/Jamo.lean:11 [direct], UnicodeData/Core/Jamo.lean:12 [direct], UnicodeData/Core/Jamo.lean:20 [direct], UnicodeData/Core/Jamo.lean:23 [direct] (4 matches) |
| `data/ucd/core/LineBreak.txt` | used | UnicodeData/Auxiliary/BreakProperties.lean:25 [direct], UnicodeData/Auxiliary/BreakProperties.lean:26 [direct], UnicodeData/Auxiliary/BreakProperties.lean:58 [direct], UnicodeData/Auxiliary/BreakProperties.lean:64 [direct], ... (9 matches) |
| `data/ucd/core/NameAliases.txt` | used | UnicodeData/Core/NameAliases.lean:11 [direct], UnicodeData/Core/NameAliases.lean:12 [direct], UnicodeData/Core/NameAliases.lean:21 [direct], UnicodeData/Core/NameAliases.lean:24 [direct] (4 matches) |
| `data/ucd/core/NamedSequences.txt` | used | UnicodeData/Core/NamedSequences.lean:11 [direct], UnicodeData/Core/NamedSequences.lean:12 [direct], UnicodeData/Core/NamedSequences.lean:20 [direct], UnicodeData/Core/NamedSequences.lean:23 [direct] (4 matches) |
| `data/ucd/core/NamedSequencesProv.txt` | used | UnicodeData/Core/NamedSequencesProv.lean:11 [direct], UnicodeData/Core/NamedSequencesProv.lean:12 [direct], UnicodeData/Core/NamedSequencesProv.lean:20 [direct], UnicodeData/Core/NamedSequencesProv.lean:23 [direct] (4 matches) |
| `data/ucd/core/NormalizationCorrections.txt` | used | UnicodeData/Core/NormalizationCorrections.lean:11 [direct], UnicodeData/Core/NormalizationCorrections.lean:12 [direct], UnicodeData/Core/NormalizationCorrections.lean:22 [direct], UnicodeData/Core/NormalizationCorrections.lean:25 [direct] (4 matches) |
| `data/ucd/core/NushuSources.txt` | used | UnicodeData/Core/NushuSources.lean:11 [direct], UnicodeData/Core/NushuSources.lean:12 [direct], UnicodeData/Core/NushuSources.lean:14 [direct], UnicodeData/Core/NushuSources.lean:17 [direct] (4 matches) |
| `data/ucd/core/PropertyAliases.txt` | used | UnicodeData/Core/PropertyAliases.lean:18 [direct], UnicodeData/Core/PropertyAliases.lean:19 [direct], UnicodeData/Core/PropertyAliases.lean:22 [direct] (3 matches) |
| `data/ucd/core/PropertyValueAliases.txt` | used | UnicodeData/Core/PropertyValueAliases.lean:13 [direct], UnicodeData/Core/PropertyValueAliases.lean:16 [direct] (2 matches) |
| `data/ucd/core/PropList.txt` | used | UnicodeBasic.lean:527 [direct], UnicodeBasic.lean:1071 [direct], UnicodeData/Core/PropList.lean:11 [direct], UnicodeData/Core/PropList.lean:58 [direct], ... (23 matches) |
| `data/ucd/core/ScriptExtensions.txt` | used | UnicodeData/Core/ScriptExtensions.lean:15 [direct], UnicodeData/Core/ScriptExtensions.lean:16 [direct], UnicodeData/Core/ScriptExtensions.lean:19 [direct], UnicodeData/Core/ScriptExtensions.lean:26 [direct] (4 matches) |
| `data/ucd/core/Scripts.txt` | used | UnicodeData/Core/Scripts.lean:15 [direct], UnicodeData/Core/Scripts.lean:16 [direct], UnicodeData/Core/Scripts.lean:19 [direct], UnicodeData/Core/Scripts.lean:26 [direct] (4 matches) |
| `data/ucd/core/SpecialCasing.txt` | used | UnicodeData/Core/SpecialCasing.lean:11 [direct], UnicodeData/Core/SpecialCasing.lean:12 [direct], UnicodeData/Core/SpecialCasing.lean:23 [direct], UnicodeData/Core/SpecialCasing.lean:26 [direct] (4 matches) |
| `data/ucd/core/StandardizedVariants.txt` | used | UnicodeData/Core/StandardizedVariants.lean:11 [direct], UnicodeData/Core/StandardizedVariants.lean:12 [direct], UnicodeData/Core/StandardizedVariants.lean:21 [direct], UnicodeData/Core/StandardizedVariants.lean:24 [direct] (4 matches) |
| `data/ucd/core/TangutSources.txt` | used | UnicodeData/Core/TangutSources.lean:11 [direct], UnicodeData/Core/TangutSources.lean:12 [direct], UnicodeData/Core/TangutSources.lean:14 [direct], UnicodeData/Core/TangutSources.lean:17 [direct] (4 matches) |
| `data/ucd/core/UnicodeData.txt` | used | UnicodeData/Basic.lean:13 [direct], UnicodeData/Basic.lean:115 [direct], UnicodeData/Basic.lean:116 [direct], UnicodeData/Basic.lean:118 [direct], ... (11 matches) |
| `data/ucd/core/Unikemet.txt` | used | UnicodeData/Core/Unikemet.lean:11 [direct], UnicodeData/Core/Unikemet.lean:12 [direct], UnicodeData/Core/Unikemet.lean:14 [direct], UnicodeData/Core/Unikemet.lean:17 [direct] (4 matches) |
| `data/ucd/core/USourceData.txt` | used | UnicodeData/Core/USourceData.lean:11 [direct], UnicodeData/Core/USourceData.lean:12 [direct], UnicodeData/Core/USourceData.lean:14 [direct], UnicodeData/Core/USourceData.lean:17 [direct] (4 matches) |
| `data/ucd/core/VerticalOrientation.txt` | used | UnicodeData/Core/VerticalOrientation.lean:11 [direct], UnicodeData/Core/VerticalOrientation.lean:12 [direct], UnicodeData/Core/VerticalOrientation.lean:14 [direct], UnicodeData/Core/VerticalOrientation.lean:16 [direct], ... (5 matches) |

## emoji

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/emoji/emoji-data.txt` | used | UnicodeData/Emoji/Emoji.lean:11 [direct], UnicodeData/Emoji/Emoji.lean:21 [direct], UnicodeData/Emoji/Emoji.lean:22 [direct], UnicodeData/Emoji/Emoji.lean:32 [direct] (4 matches) |
| `data/ucd/emoji/emoji-variation-sequences.txt` | used | UnicodeData/Emoji/EmojiVariationSequences.lean:11 [direct], UnicodeData/Emoji/EmojiVariationSequences.lean:12 [direct], UnicodeData/Emoji/EmojiVariationSequences.lean:20 [direct] (3 matches) |

## extracted

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/extracted/DerivedBidiClass.txt` | used | UnicodeData/Extracted/DerivedBidiClass.lean:12 [direct], UnicodeData/Extracted/DerivedBidiClass.lean:13 [direct], UnicodeData/Extracted/DerivedBidiClass.lean:22 [direct], UnicodeData/Extracted/DerivedBidiClass.lean:24 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedBinaryProperties.txt` | used | UnicodeData/Extracted/DerivedBinaryProperties.lean:11 [direct], UnicodeData/Extracted/DerivedBinaryProperties.lean:12 [direct], UnicodeData/Extracted/DerivedBinaryProperties.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedCombiningClass.txt` | used | UnicodeData/Extracted/DerivedCombiningClass.lean:11 [direct], UnicodeData/Extracted/DerivedCombiningClass.lean:12 [direct], UnicodeData/Extracted/DerivedCombiningClass.lean:16 [direct] (3 matches) |
| `data/ucd/extracted/DerivedDecompositionType.txt` | used | UnicodeData/Extracted/DerivedDecompositionType.lean:11 [direct], UnicodeData/Extracted/DerivedDecompositionType.lean:12 [direct], UnicodeData/Extracted/DerivedDecompositionType.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedEastAsianWidth.txt` | used | UnicodeData/Extracted/DerivedEastAsianWidth.lean:11 [direct], UnicodeData/Extracted/DerivedEastAsianWidth.lean:12 [direct] (2 matches) |
| `data/ucd/extracted/DerivedGeneralCategory.txt` | used | UnicodeData/Extracted/DerivedGeneralCategory.lean:11 [direct], UnicodeData/Extracted/DerivedGeneralCategory.lean:12 [direct], UnicodeData/Extracted/DerivedGeneralCategory.lean:14 [direct], UnicodeData/Extracted/DerivedGeneralCategory.lean:16 [direct] (4 matches) |
| `data/ucd/extracted/DerivedJoiningGroup.txt` | used | UnicodeData/Extracted/DerivedJoiningGroup.lean:11 [direct], UnicodeData/Extracted/DerivedJoiningGroup.lean:12 [direct], UnicodeData/Extracted/DerivedJoiningGroup.lean:29 [direct], UnicodeData/Extracted/DerivedJoiningGroup.lean:35 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedJoiningType.txt` | used | UnicodeData/Extracted/DerivedJoiningType.lean:11 [direct], UnicodeData/Extracted/DerivedJoiningType.lean:12 [direct], UnicodeData/Extracted/DerivedJoiningType.lean:29 [direct], UnicodeData/Extracted/DerivedJoiningType.lean:35 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedLineBreak.txt` | used | UnicodeData/Extracted/DerivedLineBreak.lean:12 [direct], UnicodeData/Extracted/DerivedLineBreak.lean:13 [direct], UnicodeData/Extracted/DerivedLineBreak.lean:22 [direct], UnicodeData/Extracted/DerivedLineBreak.lean:24 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedName.txt` | used | UnicodeData/Extracted/DerivedName.lean:11 [direct], UnicodeData/Extracted/DerivedName.lean:12 [direct], UnicodeData/Extracted/DerivedName.lean:29 [direct], UnicodeData/Extracted/DerivedName.lean:31 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedNumericType.txt` | used | UnicodeData/Extracted/DerivedNumericType.lean:11 [direct], UnicodeData/Extracted/DerivedNumericType.lean:12 [direct], UnicodeData/Extracted/DerivedNumericType.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedNumericValues.txt` | used | UnicodeData/Extracted/DerivedNumericValues.lean:12 [direct], UnicodeData/Extracted/DerivedNumericValues.lean:13 [direct], UnicodeData/Extracted/DerivedNumericValues.lean:30 [direct], UnicodeData/Extracted/DerivedNumericValues.lean:42 [direct], ... (5 matches) |

## unihan

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/unihan/Unihan_DictionaryIndices.txt` | used | UnicodeData/Unihan/UnihanDictionaryIndices.lean:11 [direct], UnicodeData/Unihan/UnihanDictionaryIndices.lean:12 [direct], UnicodeData/Unihan/UnihanDictionaryIndices.lean:24 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_DictionaryLikeData.txt` | used | UnicodeData/Unihan/UnihanDictionaryLikeData.lean:11 [direct], UnicodeData/Unihan/UnihanDictionaryLikeData.lean:12 [direct], UnicodeData/Unihan/UnihanDictionaryLikeData.lean:24 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_IRGSources.txt` | used | UnicodeData/Unihan/UnihanIRGSources.lean:12 [direct], UnicodeData/Unihan/UnihanIRGSources.lean:13 [direct], UnicodeData/Unihan/UnihanIRGSources.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_NumericValues.txt` | used | UnicodeData/Unihan/UnihanNumericValues.lean:12 [direct], UnicodeData/Unihan/UnihanNumericValues.lean:13 [direct], UnicodeData/Unihan/UnihanNumericValues.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_OtherMappings.txt` | used | UnicodeData/Unihan/UnihanOtherMappings.lean:12 [direct], UnicodeData/Unihan/UnihanOtherMappings.lean:13 [direct], UnicodeData/Unihan/UnihanOtherMappings.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_RadicalStrokeCounts.txt` | used | UnicodeData/Unihan/UnihanRadicalStrokeCounts.lean:12 [direct], UnicodeData/Unihan/UnihanRadicalStrokeCounts.lean:13 [direct], UnicodeData/Unihan/UnihanRadicalStrokeCounts.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_Readings.txt` | used | UnicodeData/Unihan/UnihanReadings.lean:12 [direct], UnicodeData/Unihan/UnihanReadings.lean:13 [direct], UnicodeData/Unihan/UnihanReadings.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_Variants.txt` | used | UnicodeData/Unihan/UnihanVariants.lean:12 [direct], UnicodeData/Unihan/UnihanVariants.lean:13 [direct], UnicodeData/Unihan/UnihanVariants.lean:25 [direct] (3 matches) |

