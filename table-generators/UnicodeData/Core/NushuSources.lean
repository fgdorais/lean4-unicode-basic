/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `NushuSources.txt` -/
def NushuSources.txt := include_str "../../data-ucd/core/NushuSources.txt"

/-- Parsed `NushuSources.txt` records. -/
public def NushuSources.data : Array (Array String) := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString NushuSources.txt
  stream := {stream with isUnihan := true}
  for record in stream do
    data := data.push (record.map (fun s => s.copy))
  return data

end Unicode
