# UCD TXT Usage

Generated from a repo scan of `data/ucd/**/*.txt` against Lean library files in `UnicodeBasic/` and `UnicodeData/`.

## Summary

- Total txt files: 69
- Used by Lean library: 15
- Unused: 54

## auxiliary

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/auxiliary/GraphemeBreakProperty.txt` | used | UnicodeData/BreakProperties.lean:19 [direct], UnicodeData/BreakProperties.lean:20 [direct], UnicodeData/BreakProperties.lean:31 [direct], UnicodeData/BreakProperties.lean:37 [direct] (4 matches) |
| `data/ucd/auxiliary/GraphemeBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/LineBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/SentenceBreakProperty.txt` | used | UnicodeData/BreakProperties.lean:23 [direct], UnicodeData/BreakProperties.lean:24 [direct], UnicodeData/BreakProperties.lean:49 [direct], UnicodeData/BreakProperties.lean:55 [direct] (4 matches) |
| `data/ucd/auxiliary/SentenceBreakTest.txt` | unused |  |
| `data/ucd/auxiliary/WordBreakProperty.txt` | used | UnicodeBasic.lean:825 [direct], UnicodeData/BreakProperties.lean:21 [direct], UnicodeData/BreakProperties.lean:22 [direct], UnicodeData/BreakProperties.lean:40 [direct], ... (5 matches) |
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
| `data/ucd/core/BidiMirroring.txt` | unused |  |
| `data/ucd/core/Blocks.txt` | used | UnicodeData/Blocks.lean:11 [direct], UnicodeData/Blocks.lean:12 [direct], UnicodeData/Blocks.lean:25 [direct], UnicodeData/Blocks.lean:31 [direct] (4 matches) |
| `data/ucd/core/CaseFolding.txt` | used | UnicodeData/CaseFolding.lean:18 [direct], UnicodeData/CaseFolding.lean:19 [direct], UnicodeData/CaseFolding.lean:22 [direct] (3 matches) |
| `data/ucd/core/CJKRadicals.txt` | unused |  |
| `data/ucd/core/CompositionExclusions.txt` | unused |  |
| `data/ucd/core/DerivedAge.txt` | unused |  |
| `data/ucd/core/DerivedCoreProperties.txt` | used | UnicodeData/DerivedCoreProperties.lean:11 [direct], UnicodeData/DerivedCoreProperties.lean:28 [direct], UnicodeData/DerivedCoreProperties.lean:29 [direct], UnicodeData/DerivedCoreProperties.lean:32 [direct], ... (5 matches) |
| `data/ucd/core/DerivedNormalizationProps.txt` | unused |  |
| `data/ucd/core/DoNotEmit.txt` | unused |  |
| `data/ucd/core/EastAsianWidth.txt` | unused |  |
| `data/ucd/core/EmojiSources.txt` | unused |  |
| `data/ucd/core/EquivalentUnifiedIdeograph.txt` | unused |  |
| `data/ucd/core/HangulSyllableType.txt` | unused |  |
| `data/ucd/core/IndicPositionalCategory.txt` | unused |  |
| `data/ucd/core/IndicSyllabicCategory.txt` | unused |  |
| `data/ucd/core/Jamo.txt` | unused |  |
| `data/ucd/core/LineBreak.txt` | used | UnicodeData/BreakProperties.lean:25 [direct], UnicodeData/BreakProperties.lean:26 [direct], UnicodeData/BreakProperties.lean:58 [direct], UnicodeData/BreakProperties.lean:64 [direct] (4 matches) |
| `data/ucd/core/NameAliases.txt` | unused |  |
| `data/ucd/core/NamedSequences.txt` | unused |  |
| `data/ucd/core/NamedSequencesProv.txt` | unused |  |
| `data/ucd/core/NamesList.txt` | unused |  |
| `data/ucd/core/NormalizationCorrections.txt` | unused |  |
| `data/ucd/core/NushuSources.txt` | unused |  |
| `data/ucd/core/PropertyAliases.txt` | used | UnicodeData/Aliases.lean:18 [direct], UnicodeData/Aliases.lean:19 [direct], UnicodeData/Aliases.lean:22 [direct] (3 matches) |
| `data/ucd/core/PropertyValueAliases.txt` | used | UnicodeData/Aliases.lean:63 [direct], UnicodeData/Aliases.lean:66 [direct] (2 matches) |
| `data/ucd/core/PropList.txt` | used | UnicodeBasic.lean:504 [direct], UnicodeBasic.lean:1048 [direct], UnicodeData/PropList.lean:11 [direct], UnicodeData/PropList.lean:58 [direct], ... (23 matches) |
| `data/ucd/core/ScriptExtensions.txt` | used | UnicodeData/ScriptExtensions.lean:15 [direct], UnicodeData/ScriptExtensions.lean:16 [direct], UnicodeData/ScriptExtensions.lean:19 [direct], UnicodeData/ScriptExtensions.lean:26 [direct] (4 matches) |
| `data/ucd/core/Scripts.txt` | used | UnicodeData/Scripts.lean:15 [direct], UnicodeData/Scripts.lean:16 [direct], UnicodeData/Scripts.lean:19 [direct], UnicodeData/Scripts.lean:26 [direct] (4 matches) |
| `data/ucd/core/SpecialCasing.txt` | unused |  |
| `data/ucd/core/StandardizedVariants.txt` | unused |  |
| `data/ucd/core/TangutSources.txt` | unused |  |
| `data/ucd/core/UnicodeData.txt` | used | UnicodeData/Basic.lean:12 [direct], UnicodeData/Basic.lean:114 [direct], UnicodeData/Basic.lean:115 [direct], UnicodeData/Basic.lean:117 [direct], ... (10 matches) |
| `data/ucd/core/Unikemet.txt` | unused |  |
| `data/ucd/core/USourceData.txt` | unused |  |
| `data/ucd/core/VerticalOrientation.txt` | unused |  |

## emoji

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/emoji/emoji-data.txt` | used | UnicodeData/Emoji.lean:11 [direct], UnicodeData/Emoji.lean:21 [direct], UnicodeData/Emoji.lean:22 [direct], UnicodeData/Emoji.lean:32 [direct] (4 matches) |
| `data/ucd/emoji/emoji-variation-sequences.txt` | unused |  |

## extracted

| File | Usage | Places |
| --- | --- | --- |
| `data/ucd/extracted/DerivedBidiClass.txt` | unused |  |
| `data/ucd/extracted/DerivedBinaryProperties.txt` | unused |  |
| `data/ucd/extracted/DerivedCombiningClass.txt` | unused |  |
| `data/ucd/extracted/DerivedDecompositionType.txt` | unused |  |
| `data/ucd/extracted/DerivedEastAsianWidth.txt` | unused |  |
| `data/ucd/extracted/DerivedGeneralCategory.txt` | unused |  |
| `data/ucd/extracted/DerivedJoiningGroup.txt` | unused |  |
| `data/ucd/extracted/DerivedJoiningType.txt` | unused |  |
| `data/ucd/extracted/DerivedLineBreak.txt` | unused |  |
| `data/ucd/extracted/DerivedName.txt` | unused |  |
| `data/ucd/extracted/DerivedNumericType.txt` | unused |  |
| `data/ucd/extracted/DerivedNumericValues.txt` | unused |  |

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

