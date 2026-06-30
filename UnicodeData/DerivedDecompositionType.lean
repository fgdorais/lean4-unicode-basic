/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedDecompositionType.txt` -/
def DerivedDecompositionType.txt := include_str "../data/ucd/extracted/DerivedDecompositionType.txt"

/-- Parsed canonical decomposition type ranges. -/
public def DerivedDecompositionType.data : Array (UInt32 × UInt32) := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString DerivedDecompositionType.txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in DerivedDecompositionType.txt"
    data := data.push (c₀, c₁)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32) (data : Array (UInt32 × UInt32)) (lo hi : Nat) : Bool :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      true
  else
    false

/-- Check whether the decomposition type is canonical. -/
public def lookupCanonicalDecompositionType (code : UInt32) : Bool :=
  find code DerivedDecompositionType.data 0 DerivedDecompositionType.data.size

end Unicode
