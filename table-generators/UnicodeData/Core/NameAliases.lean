/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `NameAliases.txt` -/
def NameAliases.txt := include_str "../../data-ucd/core/NameAliases.txt"

/-- A raw name alias record. -/
public structure NameAliasesEntry where
  public code : UInt32
  public alias : String
  public aliasType : String
deriving Inhabited, Repr

/-- Parsed `NameAliases.txt` records. -/
public def NameAliases.data : Array NameAliasesEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString NameAliases.txt
  for record in stream do
    data := data.push {
      code := UCD.parseUPlusField record[0]!
      alias := UCD.trimAsciiSlice record[1]!
      aliasType := UCD.trimAsciiSlice record[2]!
    }
  return data

end Unicode
