/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `SpecialCasing.txt` -/
def SpecialCasing.txt := include_str "../../data-ucd/core/SpecialCasing.txt"

/-- A raw special casing record. -/
public structure SpecialCasingEntry where
  public code : UInt32
  public lowercase : Array UInt32
  public titlecase : Array UInt32
  public uppercase : Array UInt32
  public condition : Option String
deriving Inhabited, Repr

/-- Parsed `SpecialCasing.txt` records. -/
public def SpecialCasing.data : Array SpecialCasingEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString SpecialCasing.txt
  for record in stream do
    let condition :=
      if 4 < record.size then
        let s := UCD.trimAsciiSlice record[4]!
        if s.isEmpty then none else some s
      else
        none
    data := data.push {
      code := UCD.parseUPlusField record[0]!
      lowercase := UCD.parseCodePointSequenceField record[1]!
      titlecase := UCD.parseCodePointSequenceField record[2]!
      uppercase := UCD.parseCodePointSequenceField record[3]!
      condition
    }
  return data

end Unicode
