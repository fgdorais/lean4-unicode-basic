/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `USourceData.txt` -/
def USourceData.txt := include_str "../../data-ucd/core/USourceData.txt"

/-- Parsed `USourceData.txt` records. -/
public def USourceData.data : Array (Array String) := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString USourceData.txt
  stream := {stream with isUnihan := true}
  for record in stream do
    data := data.push (record.map (fun s => s.copy))
  return data

end Unicode
