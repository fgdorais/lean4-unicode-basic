/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `Unihan_RadicalStrokeCounts.txt` -/
def UnihanRadicalStrokeCounts.txt := include_str "../../data-ucd/unihan/Unihan_RadicalStrokeCounts.txt"

/-- A single Unihan radical-stroke count record. -/
public structure UnihanRadicalStrokeCountsEntry where
  /-- Code point. -/
  public code : UInt32
  /-- Unihan field name. -/
  public field : String
  /-- Field value. -/
  public value : String
deriving Inhabited, Repr

/-- Parsed `Unihan_RadicalStrokeCounts.txt` records. -/
public def UnihanRadicalStrokeCounts.data : Array UnihanRadicalStrokeCountsEntry := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString UnihanRadicalStrokeCounts.txt
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

/-- Find all Unihan radical-stroke count records for a code point. -/
public def lookupUnihanRadicalStrokeCounts (code : UInt32) : Array (String × String) :=
  (UnihanRadicalStrokeCounts.data.filter (fun d => d.code == code)).map fun d =>
    (d.field, d.value)

/-- Find a specific Unihan radical-stroke count value for a code point. -/
public def lookupUnihanRadicalStrokeCount? (code : UInt32) (field : String) : Option String :=
  (lookupUnihanRadicalStrokeCounts code).findSome? fun x => if x.1 == field then some x.2 else none

end Unicode
