/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `NamedSequences.txt` -/
def NamedSequences.txt := include_str "../../data-ucd/core/NamedSequences.txt"

/-- A raw named sequence record. -/
public structure NamedSequencesEntry where
  public name : String
  public sequence : Array UInt32
deriving Inhabited, Repr

/-- Parsed `NamedSequences.txt` records. -/
public def NamedSequences.data : Array NamedSequencesEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString NamedSequences.txt
  for record in stream do
    data := data.push {
      name := UCD.trimAsciiSlice record[0]!
      sequence := UCD.parseCodePointSequenceField record[1]!
    }
  return data

end Unicode
