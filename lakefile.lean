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

lean_lib Test

lean_exe «test» {
  root := `Test
}

/-- Update data files from the Unicode Character Database (UCD) -/
script UpdateUCD := do
  let dataDir : FilePath := "./data"
  for file in [
      "UnicodeData.txt",
      "PropList.txt",
      "DerivedCoreProperties.txt",
      "extracted/DerivedNumericType.txt",
      "extracted/DerivedGeneralCategory.txt"] do
    let url := "https://www.unicode.org/Public/UCD/latest/ucd/" ++ file
    IO.println s!"Downloading UCD/{file}"
    let _ ← LogIO.captureLog <| download file url (dataDir/file)
  return 0
