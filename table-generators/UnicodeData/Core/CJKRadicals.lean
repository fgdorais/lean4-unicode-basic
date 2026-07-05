/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `CJKRadicals.txt` -/
def CJKRadicals.txt := include_str "../../data-ucd/core/CJKRadicals.txt"

/-- A raw CJK radical mapping. -/
public structure CJKRadicalsEntry where
  public radicalNumber : String
  public radicalCharacter : Option UInt32
  public unifiedIdeograph : UInt32
deriving Inhabited, Repr

/-- Parsed `CJKRadicals.txt` records. -/
public def CJKRadicals.data : Array CJKRadicalsEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString CJKRadicals.txt
  for record in stream do
    let radicalCharacter :=
      if record[1]!.isEmpty then none else some <| UCD.parseUPlusField record[1]!
    data := data.push {
      radicalNumber := UCD.trimAsciiSlice record[0]!
      radicalCharacter,
      unifiedIdeograph := UCD.parseUPlusField record[2]!
    }
  return data

end Unicode
