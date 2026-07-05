/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `NormalizationCorrections.txt` -/
def NormalizationCorrections.txt := include_str "../../data-ucd/core/NormalizationCorrections.txt"

/-- A raw normalization correction record. -/
public structure NormalizationCorrectionsEntry where
  public code : UInt32
  public original : UInt32
  public corrected : UInt32
  public version : String
deriving Inhabited, Repr

/-- Parsed `NormalizationCorrections.txt` records. -/
public def NormalizationCorrections.data : Array NormalizationCorrectionsEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString NormalizationCorrections.txt
  for record in stream do
    data := data.push {
      code := UCD.parseUPlusField record[0]!
      original := UCD.parseUPlusField record[1]!
      corrected := UCD.parseUPlusField record[2]!
      version := UCD.trimAsciiSlice record[3]!
    }
  return data

end Unicode
