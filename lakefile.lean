/-
Copyright © 2023-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open System Lake DSL

package UnicodeBasic where
  description := "Basic Unicode support for Lean 4"
  keywords := #["unicode"]
  reservoir := true
  precompileModules := true

target UnicodeCLib pkg : FilePath := do
  let mut oFiles : Array (Job FilePath) := #[]
  for file in (← (pkg.dir / "UnicodeCLib").readDir) do
    if file.path.extension == some "c" then
      let obj := pkg.buildDir / "UnicodeCLib" / ((file.fileName.dropSuffix ".c" |>.copy) ++ ".o")
      let src ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "UnicodeCLib").toString, "-O", "-fPIC"]
      oFiles := oFiles.push <| ← buildO obj src weakArgs
  let name := nameToStaticLib "unicodeclib"
  buildStaticLib (pkg.sharedLibDir / name) oFiles

extern_lib libunicodeclib := UnicodeCLib.fetch

lean_lib UnicodeBasicSupport where
  roots := #[]
  globs := #[
    `UnicodeBasic.CharacterDatabase,
    `UnicodeBasic.Hangul,
    `UnicodeBasic.Types
  ]

@[default_target]
lean_lib UnicodeBasic where
  roots := #[]
  globs := #[
    `UnicodeBasic,
    `UnicodeBasic.TableLookup
  ]
  precompileModules := true
  moreLinkObjs := #[UnicodeCLib]

lean_lib UnicodeData where
  roots := #[]
  globs := (#[
    Glob.one `UnicodeData,
    Glob.one `UnicodeData.Basic,
    Glob.one `UnicodeData.UcdParse,
    Glob.one `UnicodeData.Auxiliary.BreakProperties,
    Glob.one `UnicodeData.Core.ArabicShaping,
    Glob.one `UnicodeData.Core.BidiBrackets,
    Glob.one `UnicodeData.Core.BidiMirroring,
    Glob.one `UnicodeData.Core.Blocks,
    Glob.one `UnicodeData.Core.CJKRadicals,
    Glob.one `UnicodeData.Core.CaseFolding,
    Glob.one `UnicodeData.Core.CompositionExclusions,
    Glob.one `UnicodeData.Core.DerivedAge,
    Glob.one `UnicodeData.Core.DerivedCoreProperties,
    Glob.one `UnicodeData.Core.DerivedNormalizationProps,
    Glob.one `UnicodeData.Core.EmojiSources,
    Glob.one `UnicodeData.Core.EquivalentUnifiedIdeograph,
    Glob.one `UnicodeData.Core.HangulSyllableType,
    Glob.one `UnicodeData.Core.IndicPositionalCategory,
    Glob.one `UnicodeData.Core.IndicSyllabicCategory,
    Glob.one `UnicodeData.Core.Jamo,
    Glob.one `UnicodeData.Core.NameAliases,
    Glob.one `UnicodeData.Core.NamedSequences,
    Glob.one `UnicodeData.Core.NamedSequencesProv,
    Glob.one `UnicodeData.Core.NormalizationCorrections,
    Glob.one `UnicodeData.Core.NushuSources,
    Glob.one `UnicodeData.Core.PropertyAliases,
    Glob.one `UnicodeData.Core.PropertyValueAliases,
    Glob.one `UnicodeData.Core.PropList,
    Glob.one `UnicodeData.Core.ScriptExtensions,
    Glob.one `UnicodeData.Core.Scripts,
    Glob.one `UnicodeData.Core.SpecialCasing,
    Glob.one `UnicodeData.Core.StandardizedVariants,
    Glob.one `UnicodeData.Core.TangutSources,
    Glob.one `UnicodeData.Core.USourceData,
    Glob.one `UnicodeData.Core.Unikemet,
    Glob.one `UnicodeData.Core.VerticalOrientation,
    Glob.one `UnicodeData.Emoji.Emoji,
    Glob.one `UnicodeData.Emoji.EmojiVariationSequences,
    Glob.one `UnicodeData.Extracted.DerivedBidiClass,
    Glob.one `UnicodeData.Extracted.DerivedBinaryProperties,
    Glob.one `UnicodeData.Extracted.DerivedCombiningClass,
    Glob.one `UnicodeData.Extracted.DerivedDecompositionType,
    Glob.one `UnicodeData.Extracted.DerivedEastAsianWidth,
    Glob.one `UnicodeData.Extracted.DerivedGeneralCategory,
    Glob.one `UnicodeData.Extracted.DerivedJoiningGroup,
    Glob.one `UnicodeData.Extracted.DerivedJoiningType,
    Glob.one `UnicodeData.Extracted.DerivedLineBreak,
    Glob.one `UnicodeData.Extracted.DerivedName,
    Glob.one `UnicodeData.Extracted.DerivedNumericType,
    Glob.one `UnicodeData.Extracted.DerivedNumericValues,
    Glob.one `UnicodeData.Unihan.UnihanDictionaryIndices,
    Glob.one `UnicodeData.Unihan.UnihanDictionaryLikeData,
    Glob.one `UnicodeData.Unihan.UnihanIRGSources,
    Glob.one `UnicodeData.Unihan.UnihanNumericValues,
    Glob.one `UnicodeData.Unihan.UnihanOtherMappings,
    Glob.one `UnicodeData.Unihan.UnihanRadicalStrokeCounts,
    Glob.one `UnicodeData.Unihan.UnihanReadings,
    Glob.one `UnicodeData.Unihan.UnihanVariants
  ] : Array Glob)

lean_lib UnicodeDataTest where
  roots := #[]
  globs := #[
    Glob.one `UnicodeDataTest.Auxiliary.Common,
    Glob.one `UnicodeDataTest.Auxiliary.Grapheme,
    Glob.one `UnicodeDataTest.Auxiliary.Segmentation,
    Glob.one `UnicodeDataTest.Common.Types,
    Glob.one `UnicodeDataTest.Common.Failure,
    Glob.one `UnicodeDataTest.Common.Parse,
    Glob.one `UnicodeDataTest.Auxiliary.Data.GraphemeBreakTest,
    Glob.one `UnicodeDataTest.Auxiliary.Data.LineBreakTest,
    Glob.one `UnicodeDataTest.Auxiliary.Data.SentenceBreakTest,
    Glob.one `UnicodeDataTest.Auxiliary.Data.WordBreakTest,
    Glob.one `UnicodeDataTest.Auxiliary.Test,
    Glob.one `UnicodeDataTest.Conformance.Data.BidiCharacterTest,
    Glob.one `UnicodeDataTest.Conformance.Data.BidiTest,
    Glob.one `UnicodeDataTest.Conformance.Data.NormalizationTest,
    Glob.one `UnicodeDataTest.Conformance.Normalization,
    Glob.one `UnicodeDataTest.Conformance.Test
  ]

lean_exe lookup
lean_exe testConformance

lean_exe makeTables where
  moreLinkObjs := #[UnicodeCLib]

lean_exe makeCLib where
  moreLinkObjs := #[UnicodeCLib]

@[test_driver]
lean_exe testTables
