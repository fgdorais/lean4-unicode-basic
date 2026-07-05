/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `EquivalentUnifiedIdeograph.txt` -/
def EquivalentUnifiedIdeograph.txt := include_str "../../data-ucd/core/EquivalentUnifiedIdeograph.txt"

/-- A raw equivalent unified ideograph record. -/
public structure EquivalentUnifiedIdeographEntry where
  public start : UInt32
  public stop : UInt32
  public equivalent : UInt32
deriving Inhabited, Repr

/-- Parsed `EquivalentUnifiedIdeograph.txt` records. -/
public def EquivalentUnifiedIdeograph.data : Array EquivalentUnifiedIdeographEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString EquivalentUnifiedIdeograph.txt
  for record in stream do
    let (c₀, c₁) := UCD.parseRangeField record[0]!.copy
    data := data.push {
      start := c₀
      stop := c₁
      equivalent := UCD.parseUPlusField record[1]!
    }
  return data

end Unicode
