/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `Unikemet.txt` -/
def Unikemet.txt := include_str "../../data-ucd/core/Unikemet.txt"

/-- Parsed `Unikemet.txt` records. -/
public def Unikemet.data : Array (Array String) := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString Unikemet.txt
  stream := {stream with isUnihan := true}
  for record in stream do
    data := data.push (record.map (fun s => s.copy))
  return data

end Unicode
