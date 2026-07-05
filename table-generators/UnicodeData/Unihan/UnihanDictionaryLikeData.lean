/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `Unihan_DictionaryLikeData.txt` -/
def UnihanDictionaryLikeData.txt := include_str "../../data-ucd/unihan/Unihan_DictionaryLikeData.txt"

/-- A single Unihan dictionary-like data record. -/
public structure UnihanDictionaryLikeDataEntry where
  /-- Code point. -/
  public code : UInt32
  /-- Unihan field name. -/
  public field : String
  /-- Field value. -/
  public value : String
deriving Inhabited, Repr

/-- Parsed `Unihan_DictionaryLikeData.txt` records. -/
public def UnihanDictionaryLikeData.data : Array UnihanDictionaryLikeDataEntry := Id.run do
  let mut data := #[]
  let mut stream := UCDStream.ofString UnihanDictionaryLikeData.txt
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

end Unicode
