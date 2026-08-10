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

-- temporary fix for Windows
meta if System.Platform.isWindows then
extern_lib libunicodeclib := UnicodeCLib.fetch

@[default_target]
lean_lib UnicodeBasic where
  moreLinkObjs := #[UnicodeCLib]

lean_exe lookup
