/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `ArabicShaping.txt` -/
def ArabicShaping.txt := include_str "../../data-ucd/core/ArabicShaping.txt"

/-- A raw Arabic shaping record. -/
public structure ArabicShapingEntry where
  public code : UInt32
  public schematicName : String
  public joiningType : String
  public joiningGroup : String
deriving Inhabited, Repr

/-- Parsed `ArabicShaping.txt` records. -/
public def ArabicShaping.data : Array ArabicShapingEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString ArabicShaping.txt
  for record in stream do
    data := data.push {
      code := UCD.parseUPlusField record[0]!
      schematicName := UCD.trimAsciiSlice record[1]!
      joiningType := UCD.trimAsciiSlice record[2]!
      joiningGroup := UCD.trimAsciiSlice record[3]!
    }
  return data

end Unicode
