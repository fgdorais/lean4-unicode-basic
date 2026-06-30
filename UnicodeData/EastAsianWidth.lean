/-
Copyright © 2025-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `EastAsianWidth.txt` -/
def EastAsianWidth.txt := include_str "../data/ucd/core/EastAsianWidth.txt"

/-- Parsed `EastAsianWidth.txt` records. -/
public def EastAsianWidth.data : Array (UInt32 × UInt32 × EastAsianWidth) := Id.run do
  let stream := UCDStream.ofString EastAsianWidth.txt
  let mut data := #[]
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in EastAsianWidth.txt"
    data := data.push (c₀, c₁, EastAsianWidth.ofAbbrev! record[1]!)
  return data

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × EastAsianWidth)) (lo hi : Nat) : Option EastAsianWidth :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, ew) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some ew
  else
    none

/-- Find the East Asian width for a code point, if it is explicitly listed. -/
public def lookupEastAsianWidth? (code : UInt32) : Option EastAsianWidth :=
  find code EastAsianWidth.data 0 EastAsianWidth.data.size

/-- Find the East Asian width for a code point, defaulting to `N`. -/
public def lookupEastAsianWidth (code : UInt32) : EastAsianWidth :=
  lookupEastAsianWidth? code |>.getD .neutral

end Unicode
