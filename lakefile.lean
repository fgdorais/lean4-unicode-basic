/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package UnicodeBasic

@[default_target]
lean_lib UnicodeBasic {
  precompileModules := true
}

lean_exe UnicodeTool

-- Download datafile from the Unicode Character Database (UCD)
script downloadUCD (args) do
  let dir : FilePath := "./data"
  let url := "https://www.unicode.org/Public/UCD/latest/ucd/"
  let mut err : ExitCode := 0
  for file in args do
    IO.print s!"Downloading UCD/{file} ... "
    match ← download (url ++ file) (dir/file) |>.run with
    | .ok _ _ => IO.println "Done."
    | .error _ _ => IO.println "Failed!"; err := err + 1
  return err

-- Update data files from the Unicode Character Database (UCD)
script updateUCD do downloadUCD ["UnicodeData.txt", "PropList.txt"]
