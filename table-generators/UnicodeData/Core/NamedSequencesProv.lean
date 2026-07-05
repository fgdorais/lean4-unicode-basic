/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `NamedSequencesProv.txt` -/
def NamedSequencesProv.txt := include_str "../../data-ucd/core/NamedSequencesProv.txt"

/-- A raw provisional named sequence record. -/
public structure NamedSequencesProvEntry where
  public name : String
  public sequence : Array UInt32
deriving Inhabited, Repr

/-- Parsed `NamedSequencesProv.txt` records. -/
public def NamedSequencesProv.data : Array NamedSequencesProvEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString NamedSequencesProv.txt
  for record in stream do
    data := data.push {
      name := UCD.trimAsciiSlice record[0]!
      sequence := UCD.parseCodePointSequenceField record[1]!
    }
  return data

end Unicode
