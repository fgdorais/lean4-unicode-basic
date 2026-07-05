/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `Jamo.txt` -/
def Jamo.txt := include_str "../../data-ucd/core/Jamo.txt"

/-- A raw Jamo short-name record. -/
public structure JamoEntry where
  public code : UInt32
  public shortName : String
deriving Inhabited, Repr

/-- Parsed `Jamo.txt` records. -/
public def Jamo.data : Array JamoEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString Jamo.txt
  for record in stream do
    data := data.push {
      code := UCD.parseUPlusField record[0]!
      shortName := UCD.trimAsciiSlice record[1]!
    }
  return data

end Unicode
