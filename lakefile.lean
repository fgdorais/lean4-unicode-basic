/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package «lean4-unicode-basic»

@[default_target]
lean_lib UnicodeBasic {
  precompileModules := true
}

lean_exe UnicodeTool

script UpdateUCD := do
  let dir : FilePath := "./data"
  for file in ["UnicodeData.txt"] do
    IO.println s!"Updating {file}"
    let url := "https://www.unicode.org/Public/UCD/latest/ucd/" ++ file

    let mut args := #["-sSO", "--remote-time"]
    if ← System.FilePath.pathExists <| dir/file then
      args := args ++ #["-z", file]
    let _ ← IO.Process.run {
      cmd := "curl"
      args := args.push url
      cwd := some dir
    }
  return 0
