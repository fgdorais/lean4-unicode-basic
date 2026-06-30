/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedGeneralCategory.txt` -/
def DerivedGeneralCategory.txt := include_str "../data/ucd/extracted/DerivedGeneralCategory.txt"

/-- Parsed `DerivedGeneralCategory.txt` ranges. -/
public def DerivedGeneralCategory.data : Array (UInt32 × UInt32 × GC) := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString DerivedGeneralCategory.txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in DerivedGeneralCategory.txt"
    data := data.push (c₀, c₁, GC.ofAbbrev! record[1]!)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × GC)) (lo hi : Nat) : Option GC :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, gc) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some gc
  else
    none

/-- Find the general category for a code point, if explicitly listed. -/
public def lookupDerivedGeneralCategory? (code : UInt32) : Option GC :=
  find code DerivedGeneralCategory.data 0 DerivedGeneralCategory.data.size

/-- Find the general category for a code point, defaulting to `Cn`. -/
public def lookupDerivedGeneralCategory (code : UInt32) : GC :=
  lookupDerivedGeneralCategory? code |>.getD .Cn

end Unicode
