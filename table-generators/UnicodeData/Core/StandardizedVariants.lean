/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `StandardizedVariants.txt` -/
def StandardizedVariants.txt := include_str "../../data-ucd/core/StandardizedVariants.txt"

/-- A raw standardized variation sequence record. -/
public structure StandardizedVariantsEntry where
  public sequence : Array UInt32
  public description : String
  public context : Option String
deriving Inhabited, Repr

/-- Parsed `StandardizedVariants.txt` records. -/
public def StandardizedVariants.data : Array StandardizedVariantsEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString StandardizedVariants.txt
  for record in stream do
    let context :=
      if 2 < record.size then
        let s := UCD.trimAsciiSlice record[2]!
        if s.isEmpty then none else some s
      else
        none
    data := data.push {
      sequence := UCD.parseCodePointSequenceField record[0]!
      description := UCD.trimAsciiSlice record[1]!
      context
    }
  return data

end Unicode
