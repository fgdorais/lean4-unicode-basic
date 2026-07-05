/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Type for case folding data -/
public structure CaseFoldingEntry where
  code : UInt32
  status : Char
  mapping : Array UInt32
deriving Inhabited, Repr

/-- Raw string from `CaseFolding.txt` -/
def CaseFolding.txt := include_str "../../data-ucd/core/CaseFolding.txt"

public initialize CaseFolding.data : Array CaseFoldingEntry ← do
  let stream := UCDStream.ofString CaseFolding.txt
  let mut arr := #[]
  for record in stream do
    let code := ofHexString! record[0]!
    let status := Char.ofUInt8 (record[1]!.getUTF8Byte! 0)
    let mapping := record[2]!.split " " |>.toArray.map ofHexString!
    arr := arr.push ⟨code, status, mapping⟩
  return arr

end Unicode
