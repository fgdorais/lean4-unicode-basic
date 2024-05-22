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

-- Update data files from the Unicode Character Database (UCD)
-- script UpdateUCD := do
--   let dataDir : FilePath := "./data"
--   for file in ["UnicodeData.txt", "PropList.txt"] do
--     let url := "https://www.unicode.org/Public/UCD/latest/ucd/" ++ file
--     IO.println s!"Downloading UCD/{file}"
--     let _ ← liftM <| ELogT.run <| download url (dataDir/file)
--   return 0
