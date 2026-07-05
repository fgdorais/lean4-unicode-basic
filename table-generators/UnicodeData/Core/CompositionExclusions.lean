/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `CompositionExclusions.txt` -/
def CompositionExclusions.txt := include_str "../../data-ucd/core/CompositionExclusions.txt"

/-- Parsed composition exclusions. -/
public def CompositionExclusions.data : Array UInt32 := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString CompositionExclusions.txt
  for record in stream do
    data := data.push (UCD.parseUPlusField record[0]!)
  return data

end Unicode
