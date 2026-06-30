/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `Blocks.txt` -/
def Blocks.txt := include_str "../data/ucd/core/Blocks.txt"

private partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

public def Blocks.data : Array (UInt32 × UInt32 × String) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString Blocks.txt
  for record in stream do
    let (start, stop) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in Blocks.txt"
    r := r.push (start, stop, record[1]!.copy)
  return r

/-- Get block name for a code point -/
public def lookupBlockName (c : UInt32) : String :=
  let table := Blocks.data
  if table.size == 0 then "No_Block" else
    if c < table[0]!.1 then "No_Block" else
      match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
      | (_, v, n) => if c ≤ v then n else "No_Block"

end Unicode
