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
  globs := #[
    `UnicodeData,
    `UnicodeData.Aliases,
    `UnicodeData.Basic,
    `UnicodeData.DerivedBidiClass,
    `UnicodeData.DerivedCombiningClass,
    `UnicodeData.DerivedBinaryProperties,
    `UnicodeData.DerivedGeneralCategory,
    `UnicodeData.DerivedLineBreak,
    `UnicodeData.DerivedAge,
    `UnicodeData.DerivedDecompositionType,
    `UnicodeData.DerivedJoiningGroup,
    `UnicodeData.DerivedNumericType,
    `UnicodeData.DerivedNumericValues,
    `UnicodeData.BidiBrackets,
    `UnicodeData.BidiMirroring,
    `UnicodeData.Blocks,
    `UnicodeData.EastAsianWidth,
    `UnicodeData.BreakProperties,
    `UnicodeData.VerticalOrientation,
    `UnicodeData.CaseFolding,
    `UnicodeData.DerivedCoreProperties,
    `UnicodeData.Emoji,
    `UnicodeData.PropList,
    `UnicodeData.ScriptExtensions,
    `UnicodeData.Scripts
  ]

lean_exe lookup

lean_exe makeTables where
  moreLinkObjs := #[UnicodeCLib]

lean_exe makeCLib where
  moreLinkObjs := #[UnicodeCLib]

@[test_driver]
lean_exe testTables
