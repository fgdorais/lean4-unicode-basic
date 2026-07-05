/-
Copyright © 2025-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.VerticalOrientation
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

namespace VerticalOrientation

/-- Raw string from `VerticalOrientation.txt` -/
public def txt := include_str "../../data-ucd/core/VerticalOrientation.txt"

/-- Parsed `VerticalOrientation.txt` records. -/
public def data : Array (UInt32 × UInt32 × VerticalOrientation) := Id.run do
  let stream := UCDStream.ofString txt
  let mut data := #[]
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in VerticalOrientation.txt"
    data := data.push (c₀, c₁, VerticalOrientation.ofAbbrev! record[1]!)
  return data

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × VerticalOrientation)) (lo hi : Nat) : Option VerticalOrientation :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, vo) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some vo
  else
    none

/-- Find the vertical orientation for a code point, if it is explicitly listed. -/
public def lookup? (code : UInt32) : Option VerticalOrientation :=
  find code data 0 data.size

/-- Find the vertical orientation for a code point, defaulting to `R`. -/
public def lookup (code : UInt32) : VerticalOrientation :=
  lookup? code |>.getD .rotated

end VerticalOrientation

end Unicode
