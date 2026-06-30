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
    Glob.one `UnicodeData.Aliases,
    Glob.one `UnicodeData.Basic,
    Glob.one `UnicodeData.UcdParse,
    Glob.one `UnicodeData.ArabicShaping,
    Glob.one `UnicodeData.CJKRadicals,
    Glob.one `UnicodeData.CompositionExclusions,
    Glob.one `UnicodeData.DerivedBidiClass,
    Glob.one `UnicodeData.DerivedCombiningClass,
    Glob.one `UnicodeData.DerivedBinaryProperties,
    Glob.one `UnicodeData.DerivedGeneralCategory,
    Glob.one `UnicodeData.DerivedLineBreak,
    Glob.one `UnicodeData.DerivedAge,
    Glob.one `UnicodeData.DerivedDecompositionType,
    Glob.one `UnicodeData.DerivedJoiningGroup,
    Glob.one `UnicodeData.DerivedJoiningType,
    Glob.one `UnicodeData.DerivedName,
    Glob.one `UnicodeData.DerivedNormalizationProps,
    Glob.one `UnicodeData.DerivedNumericType,
    Glob.one `UnicodeData.DerivedNumericValues,
    Glob.one `UnicodeData.EmojiSources,
    Glob.one `UnicodeData.EquivalentUnifiedIdeograph,
    Glob.one `UnicodeData.HangulSyllableType,
    Glob.one `UnicodeData.IndicPositionalCategory,
    Glob.one `UnicodeData.IndicSyllabicCategory,
    Glob.one `UnicodeData.Jamo,
    Glob.one `UnicodeData.NameAliases,
    Glob.one `UnicodeData.NamedSequences,
    Glob.one `UnicodeData.NamedSequencesProv,
    Glob.one `UnicodeData.NormalizationCorrections,
    Glob.one `UnicodeData.SpecialCasing,
    Glob.one `UnicodeData.StandardizedVariants,
    Glob.one `UnicodeData.EmojiVariationSequences,
    Glob.one `UnicodeData.TangutSources,
    Glob.one `UnicodeData.NushuSources,
    Glob.one `UnicodeData.Unikemet,
    Glob.one `UnicodeData.USourceData,
    Glob.one `UnicodeData.UnihanDictionaryIndices,
    Glob.one `UnicodeData.UnihanDictionaryLikeData,
    Glob.one `UnicodeData.UnihanIRGSources,
    Glob.one `UnicodeData.UnihanNumericValues,
    Glob.one `UnicodeData.UnihanOtherMappings,
    Glob.one `UnicodeData.UnihanRadicalStrokeCounts,
    Glob.one `UnicodeData.UnihanReadings,
    Glob.one `UnicodeData.UnihanVariants,
    Glob.one `UnicodeData.BidiBrackets,
    Glob.one `UnicodeData.BidiMirroring,
    Glob.one `UnicodeData.Blocks,
    Glob.one `UnicodeData.EastAsianWidth,
    Glob.one `UnicodeData.BreakProperties,
    Glob.one `UnicodeData.VerticalOrientation,
    Glob.one `UnicodeData.CaseFolding,
    Glob.one `UnicodeData.DerivedCoreProperties,
    Glob.one `UnicodeData.Emoji,
    Glob.one `UnicodeData.PropList,
    Glob.one `UnicodeData.ScriptExtensions,
    Glob.one `UnicodeData.Scripts
  ] : Array Glob)

lean_exe lookup

lean_exe makeTables where
  moreLinkObjs := #[UnicodeCLib]

lean_exe makeCLib where
  moreLinkObjs := #[UnicodeCLib]

@[test_driver]
lean_exe testTables
