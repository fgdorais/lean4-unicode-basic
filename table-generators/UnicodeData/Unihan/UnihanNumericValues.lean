/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `Unihan_NumericValues.txt` -/
def UnihanNumericValues.txt := include_str "../../data-ucd/unihan/Unihan_NumericValues.txt"

/-- A single Unihan numeric value record. -/
public structure UnihanNumericValuesEntry where
  /-- Code point. -/
  public code : UInt32
  /-- Unihan field name. -/
  public field : String
  /-- Field value. -/
  public value : String
deriving Inhabited, Repr

/-- Parsed `Unihan_NumericValues.txt` records. -/
public def UnihanNumericValues.data : Array UnihanNumericValuesEntry := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString UnihanNumericValues.txt
  stream := {stream with isUnihan := true}
  for record in stream do
    if record.size < 3 then
      continue
    else
      let code := ofHexString! record[0]!
      let field := record[1]!.copy
      let value := record[2]!.copy
      data := data.push {code, field, value}
  return data.qsort fun a b =>
    a.code < b.code || (a.code == b.code && a.field < b.field)

/-- Find all Unihan numeric value records for a code point. -/
public def lookupUnihanNumericValues (code : UInt32) : Array (String × String) :=
  (UnihanNumericValues.data.filter (fun d => d.code == code)).map fun d =>
    (d.field, d.value)

/-- Find a specific Unihan numeric value for a code point. -/
public def lookupUnihanNumericValue? (code : UInt32) (field : String) : Option String :=
  (lookupUnihanNumericValues code).findSome? fun x => if x.1 == field then some x.2 else none

end Unicode
