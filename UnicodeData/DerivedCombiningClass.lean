/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedCombiningClass.txt` -/
def DerivedCombiningClass.txt := include_str "../data/ucd/extracted/DerivedCombiningClass.txt"

/-- Parsed non-zero combining class ranges. -/
public def DerivedCombiningClass.data : Array (UInt32 × UInt32 × Nat) := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString DerivedCombiningClass.txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in DerivedCombiningClass.txt"
    let ccc := record[1]!.toNat!
    if ccc != 0 then
      data := data.push (c₀, c₁, ccc)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × Nat)) (lo hi : Nat) : Option Nat :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, ccc) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some ccc
  else
    none

/-- Find the canonical combining class for a code point, if explicitly listed. -/
public def lookupDerivedCombiningClass? (code : UInt32) : Option Nat :=
  find code DerivedCombiningClass.data 0 DerivedCombiningClass.data.size

/-- Find the canonical combining class for a code point, defaulting to `0`. -/
public def lookupDerivedCombiningClass (code : UInt32) : Nat :=
  lookupDerivedCombiningClass? code |>.getD 0

end Unicode
