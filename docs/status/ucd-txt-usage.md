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
| `data/ucd/core/ArabicShaping.txt` | used | UnicodeData/ArabicShaping.lean:11 [direct], UnicodeData/ArabicShaping.lean:12 [direct], UnicodeData/ArabicShaping.lean:22 [direct], UnicodeData/ArabicShaping.lean:25 [direct] (4 matches) |
| `data/ucd/core/BidiBrackets.txt` | used | UnicodeData/BidiBrackets.lean:11 [direct], UnicodeData/BidiBrackets.lean:17 [direct], UnicodeData/BidiBrackets.lean:18 [direct], UnicodeData/BidiBrackets.lean:31 [direct] (4 matches) |
| `data/ucd/core/BidiMirroring.txt` | used | UnicodeData/BidiMirroring.lean:12 [direct], UnicodeData/BidiMirroring.lean:13 [direct], UnicodeData/BidiMirroring.lean:15 [direct], UnicodeData/BidiMirroring.lean:17 [direct] (4 matches) |
| `data/ucd/core/Blocks.txt` | used | UnicodeData/Blocks.lean:11 [direct], UnicodeData/Blocks.lean:12 [direct], UnicodeData/Blocks.lean:25 [direct], UnicodeData/Blocks.lean:31 [direct] (4 matches) |
| `data/ucd/core/CaseFolding.txt` | used | UnicodeData/CaseFolding.lean:18 [direct], UnicodeData/CaseFolding.lean:19 [direct], UnicodeData/CaseFolding.lean:22 [direct] (3 matches) |
| `data/ucd/core/CJKRadicals.txt` | used | UnicodeData/CJKRadicals.lean:11 [direct], UnicodeData/CJKRadicals.lean:12 [direct], UnicodeData/CJKRadicals.lean:21 [direct], UnicodeData/CJKRadicals.lean:24 [direct] (4 matches) |
| `data/ucd/core/CompositionExclusions.txt` | used | UnicodeData/CompositionExclusions.lean:11 [direct], UnicodeData/CompositionExclusions.lean:12 [direct], UnicodeData/CompositionExclusions.lean:17 [direct] (3 matches) |
| `data/ucd/core/DerivedAge.txt` | used | UnicodeData/DerivedAge.lean:11 [direct], UnicodeData/DerivedAge.lean:12 [direct], UnicodeData/DerivedAge.lean:14 [direct], UnicodeData/DerivedAge.lean:16 [direct], ... (5 matches) |
| `data/ucd/core/DerivedCoreProperties.txt` | used | UnicodeData/DerivedCoreProperties.lean:11 [direct], UnicodeData/DerivedCoreProperties.lean:28 [direct], UnicodeData/DerivedCoreProperties.lean:29 [direct], UnicodeData/DerivedCoreProperties.lean:32 [direct], ... (5 matches) |
| `data/ucd/core/DerivedNormalizationProps.txt` | used | UnicodeData/DerivedNormalizationProps.lean:11 [direct], UnicodeData/DerivedNormalizationProps.lean:12 [direct], UnicodeData/DerivedNormalizationProps.lean:29 [direct], UnicodeData/DerivedNormalizationProps.lean:40 [direct], ... (6 matches) |
| `data/ucd/core/EastAsianWidth.txt` | used | UnicodeData/EastAsianWidth.lean:11 [direct], UnicodeData/EastAsianWidth.lean:12 [direct], UnicodeData/EastAsianWidth.lean:14 [direct], UnicodeData/EastAsianWidth.lean:16 [direct] (4 matches) |
| `data/ucd/core/EmojiSources.txt` | used | UnicodeData/EmojiSources.lean:11 [direct], UnicodeData/EmojiSources.lean:12 [direct], UnicodeData/EmojiSources.lean:22 [direct], UnicodeData/EmojiSources.lean:25 [direct] (4 matches) |
| `data/ucd/core/EquivalentUnifiedIdeograph.txt` | used | UnicodeData/EquivalentUnifiedIdeograph.lean:11 [direct], UnicodeData/EquivalentUnifiedIdeograph.lean:12 [direct], UnicodeData/EquivalentUnifiedIdeograph.lean:21 [direct], UnicodeData/EquivalentUnifiedIdeograph.lean:24 [direct] (4 matches) |
| `data/ucd/core/HangulSyllableType.txt` | used | UnicodeData/HangulSyllableType.lean:11 [direct], UnicodeData/HangulSyllableType.lean:12 [direct], UnicodeData/HangulSyllableType.lean:14 [direct], UnicodeData/HangulSyllableType.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/IndicPositionalCategory.txt` | used | UnicodeData/IndicPositionalCategory.lean:11 [direct], UnicodeData/IndicPositionalCategory.lean:12 [direct], UnicodeData/IndicPositionalCategory.lean:14 [direct], UnicodeData/IndicPositionalCategory.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/IndicSyllabicCategory.txt` | used | UnicodeData/IndicSyllabicCategory.lean:11 [direct], UnicodeData/IndicSyllabicCategory.lean:12 [direct], UnicodeData/IndicSyllabicCategory.lean:14 [direct], UnicodeData/IndicSyllabicCategory.lean:16 [direct], ... (6 matches) |
| `data/ucd/core/Jamo.txt` | used | UnicodeData/Jamo.lean:11 [direct], UnicodeData/Jamo.lean:12 [direct], UnicodeData/Jamo.lean:20 [direct], UnicodeData/Jamo.lean:23 [direct] (4 matches) |
| `data/ucd/core/LineBreak.txt` | used | UnicodeData/BreakProperties.lean:25 [direct], UnicodeData/BreakProperties.lean:26 [direct], UnicodeData/BreakProperties.lean:58 [direct], UnicodeData/BreakProperties.lean:64 [direct], ... (9 matches) |
| `data/ucd/core/NameAliases.txt` | used | UnicodeData/NameAliases.lean:11 [direct], UnicodeData/NameAliases.lean:12 [direct], UnicodeData/NameAliases.lean:21 [direct], UnicodeData/NameAliases.lean:24 [direct] (4 matches) |
| `data/ucd/core/NamedSequences.txt` | used | UnicodeData/NamedSequences.lean:11 [direct], UnicodeData/NamedSequences.lean:12 [direct], UnicodeData/NamedSequences.lean:20 [direct], UnicodeData/NamedSequences.lean:23 [direct] (4 matches) |
| `data/ucd/core/NamedSequencesProv.txt` | used | UnicodeData/NamedSequencesProv.lean:11 [direct], UnicodeData/NamedSequencesProv.lean:12 [direct], UnicodeData/NamedSequencesProv.lean:20 [direct], UnicodeData/NamedSequencesProv.lean:23 [direct] (4 matches) |
| `data/ucd/core/NormalizationCorrections.txt` | used | UnicodeData/NormalizationCorrections.lean:11 [direct], UnicodeData/NormalizationCorrections.lean:12 [direct], UnicodeData/NormalizationCorrections.lean:22 [direct], UnicodeData/NormalizationCorrections.lean:25 [direct] (4 matches) |
| `data/ucd/core/NushuSources.txt` | used | UnicodeData/NushuSources.lean:11 [direct], UnicodeData/NushuSources.lean:12 [direct], UnicodeData/NushuSources.lean:14 [direct], UnicodeData/NushuSources.lean:17 [direct] (4 matches) |
| `data/ucd/core/PropertyAliases.txt` | used | UnicodeData/Aliases.lean:18 [direct], UnicodeData/Aliases.lean:19 [direct], UnicodeData/Aliases.lean:22 [direct] (3 matches) |
| `data/ucd/core/PropertyValueAliases.txt` | used | UnicodeData/Aliases.lean:63 [direct], UnicodeData/Aliases.lean:66 [direct] (2 matches) |
| `data/ucd/core/PropList.txt` | used | UnicodeBasic.lean:527 [direct], UnicodeBasic.lean:1071 [direct], UnicodeData/PropList.lean:11 [direct], UnicodeData/PropList.lean:58 [direct], ... (23 matches) |
| `data/ucd/core/ScriptExtensions.txt` | used | UnicodeData/ScriptExtensions.lean:15 [direct], UnicodeData/ScriptExtensions.lean:16 [direct], UnicodeData/ScriptExtensions.lean:19 [direct], UnicodeData/ScriptExtensions.lean:26 [direct] (4 matches) |
| `data/ucd/core/Scripts.txt` | used | UnicodeData/Scripts.lean:15 [direct], UnicodeData/Scripts.lean:16 [direct], UnicodeData/Scripts.lean:19 [direct], UnicodeData/Scripts.lean:26 [direct] (4 matches) |
| `data/ucd/core/SpecialCasing.txt` | used | UnicodeData/SpecialCasing.lean:11 [direct], UnicodeData/SpecialCasing.lean:12 [direct], UnicodeData/SpecialCasing.lean:23 [direct], UnicodeData/SpecialCasing.lean:26 [direct] (4 matches) |
| `data/ucd/core/StandardizedVariants.txt` | used | UnicodeData/StandardizedVariants.lean:11 [direct], UnicodeData/StandardizedVariants.lean:12 [direct], UnicodeData/StandardizedVariants.lean:21 [direct], UnicodeData/StandardizedVariants.lean:24 [direct] (4 matches) |
| `data/ucd/core/TangutSources.txt` | used | UnicodeData/TangutSources.lean:11 [direct], UnicodeData/TangutSources.lean:12 [direct], UnicodeData/TangutSources.lean:14 [direct], UnicodeData/TangutSources.lean:17 [direct] (4 matches) |
| `data/ucd/core/UnicodeData.txt` | used | UnicodeData/Basic.lean:13 [direct], UnicodeData/Basic.lean:115 [direct], UnicodeData/Basic.lean:116 [direct], UnicodeData/Basic.lean:118 [direct], ... (11 matches) |
| `data/ucd/core/Unikemet.txt` | used | UnicodeData/Unikemet.lean:11 [direct], UnicodeData/Unikemet.lean:12 [direct], UnicodeData/Unikemet.lean:14 [direct], UnicodeData/Unikemet.lean:17 [direct] (4 matches) |
| `data/ucd/core/USourceData.txt` | used | UnicodeData/USourceData.lean:11 [direct], UnicodeData/USourceData.lean:12 [direct], UnicodeData/USourceData.lean:14 [direct], UnicodeData/USourceData.lean:17 [direct] (4 matches) |
| `data/ucd/core/VerticalOrientation.txt` | used | UnicodeData/VerticalOrientation.lean:11 [direct], UnicodeData/VerticalOrientation.lean:12 [direct], UnicodeData/VerticalOrientation.lean:14 [direct], UnicodeData/VerticalOrientation.lean:16 [direct], ... (5 matches) |

## emoji

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/emoji/emoji-data.txt` | used | UnicodeData/Emoji.lean:11 [direct], UnicodeData/Emoji.lean:21 [direct], UnicodeData/Emoji.lean:22 [direct], UnicodeData/Emoji.lean:32 [direct] (4 matches) |
| `data/ucd/emoji/emoji-variation-sequences.txt` | used | UnicodeData/EmojiVariationSequences.lean:11 [direct], UnicodeData/EmojiVariationSequences.lean:12 [direct], UnicodeData/EmojiVariationSequences.lean:20 [direct] (3 matches) |

## extracted

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/extracted/DerivedBidiClass.txt` | used | UnicodeData/DerivedBidiClass.lean:12 [direct], UnicodeData/DerivedBidiClass.lean:13 [direct], UnicodeData/DerivedBidiClass.lean:22 [direct], UnicodeData/DerivedBidiClass.lean:24 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedBinaryProperties.txt` | used | UnicodeData/DerivedBinaryProperties.lean:11 [direct], UnicodeData/DerivedBinaryProperties.lean:12 [direct], UnicodeData/DerivedBinaryProperties.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedCombiningClass.txt` | used | UnicodeData/DerivedCombiningClass.lean:11 [direct], UnicodeData/DerivedCombiningClass.lean:12 [direct], UnicodeData/DerivedCombiningClass.lean:16 [direct] (3 matches) |
| `data/ucd/extracted/DerivedDecompositionType.txt` | used | UnicodeData/DerivedDecompositionType.lean:11 [direct], UnicodeData/DerivedDecompositionType.lean:12 [direct], UnicodeData/DerivedDecompositionType.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedEastAsianWidth.txt` | used | UnicodeData/EastAsianWidth.lean:11 [direct], UnicodeData/EastAsianWidth.lean:12 [direct] (2 matches) |
| `data/ucd/extracted/DerivedGeneralCategory.txt` | used | UnicodeData/DerivedGeneralCategory.lean:11 [direct], UnicodeData/DerivedGeneralCategory.lean:12 [direct], UnicodeData/DerivedGeneralCategory.lean:14 [direct], UnicodeData/DerivedGeneralCategory.lean:16 [direct] (4 matches) |
| `data/ucd/extracted/DerivedJoiningGroup.txt` | used | UnicodeData/DerivedJoiningGroup.lean:11 [direct], UnicodeData/DerivedJoiningGroup.lean:12 [direct], UnicodeData/DerivedJoiningGroup.lean:29 [direct], UnicodeData/DerivedJoiningGroup.lean:35 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedJoiningType.txt` | used | UnicodeData/DerivedJoiningType.lean:11 [direct], UnicodeData/DerivedJoiningType.lean:12 [direct], UnicodeData/DerivedJoiningType.lean:29 [direct], UnicodeData/DerivedJoiningType.lean:35 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedLineBreak.txt` | used | UnicodeData/DerivedLineBreak.lean:12 [direct], UnicodeData/DerivedLineBreak.lean:13 [direct], UnicodeData/DerivedLineBreak.lean:22 [direct], UnicodeData/DerivedLineBreak.lean:24 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedName.txt` | used | UnicodeData/DerivedName.lean:11 [direct], UnicodeData/DerivedName.lean:12 [direct], UnicodeData/DerivedName.lean:29 [direct], UnicodeData/DerivedName.lean:31 [direct], ... (5 matches) |
| `data/ucd/extracted/DerivedNumericType.txt` | used | UnicodeData/DerivedNumericType.lean:11 [direct], UnicodeData/DerivedNumericType.lean:12 [direct], UnicodeData/DerivedNumericType.lean:15 [direct] (3 matches) |
| `data/ucd/extracted/DerivedNumericValues.txt` | used | UnicodeData/DerivedNumericValues.lean:12 [direct], UnicodeData/DerivedNumericValues.lean:13 [direct], UnicodeData/DerivedNumericValues.lean:30 [direct], UnicodeData/DerivedNumericValues.lean:42 [direct], ... (5 matches) |

## unihan

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/unihan/Unihan_DictionaryIndices.txt` | used | UnicodeData/UnihanDictionaryIndices.lean:11 [direct], UnicodeData/UnihanDictionaryIndices.lean:12 [direct], UnicodeData/UnihanDictionaryIndices.lean:24 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_DictionaryLikeData.txt` | used | UnicodeData/UnihanDictionaryLikeData.lean:11 [direct], UnicodeData/UnihanDictionaryLikeData.lean:12 [direct], UnicodeData/UnihanDictionaryLikeData.lean:24 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_IRGSources.txt` | used | UnicodeData/UnihanIRGSources.lean:12 [direct], UnicodeData/UnihanIRGSources.lean:13 [direct], UnicodeData/UnihanIRGSources.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_NumericValues.txt` | used | UnicodeData/UnihanNumericValues.lean:12 [direct], UnicodeData/UnihanNumericValues.lean:13 [direct], UnicodeData/UnihanNumericValues.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_OtherMappings.txt` | used | UnicodeData/UnihanOtherMappings.lean:12 [direct], UnicodeData/UnihanOtherMappings.lean:13 [direct], UnicodeData/UnihanOtherMappings.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_RadicalStrokeCounts.txt` | used | UnicodeData/UnihanRadicalStrokeCounts.lean:12 [direct], UnicodeData/UnihanRadicalStrokeCounts.lean:13 [direct], UnicodeData/UnihanRadicalStrokeCounts.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_Readings.txt` | used | UnicodeData/UnihanReadings.lean:12 [direct], UnicodeData/UnihanReadings.lean:13 [direct], UnicodeData/UnihanReadings.lean:25 [direct] (3 matches) |
| `data/ucd/unihan/Unihan_Variants.txt` | used | UnicodeData/UnihanVariants.lean:12 [direct], UnicodeData/UnihanVariants.lean:13 [direct], UnicodeData/UnihanVariants.lean:25 [direct] (3 matches) |

