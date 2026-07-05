/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.BidiBracketType
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

namespace BidiBrackets

/-- Structure for `BidiBrackets.txt` -/
public structure BidiBracket where
  pairedBracket : UInt32
  bracketType : BidiBracketType
deriving Inhabited, Repr

/-- Raw string from `BidiBrackets.txt` -/
public def txt := include_str "../../data-ucd/core/BidiBrackets.txt"

private partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

public def data : Array (UInt32 × BidiBracket) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString txt
  for record in stream do
    let code := ofHexString! record[0]!
    let pairedBracket := ofHexString! record[1]!
    let bracketType := BidiBracketType.ofAbbrev! record[2]!
    r := r.push (code, BidiBracket.mk pairedBracket bracketType)
  return r

/-- Get bidi bracket data for a code point -/
public def lookup? (c : UInt32) : Option BidiBracket :=
  let table := data
  if table.size == 0 || c < table[0]!.1 then none else
    let d := table[find c (fun i => table[i]!.1) 0 table.usize]!
    if c = d.1 then some d.2 else none

/-- Get bidi paired bracket for a code point -/
public def lookupPairedBracket? (c : UInt32) : Option UInt32 :=
  (lookup? c).map BidiBracket.pairedBracket

/-- Get bidi paired bracket type for a code point -/
public def lookupPairedBracketType? (c : UInt32) : Option BidiBracketType :=
  (lookup? c).map BidiBracket.bracketType

end BidiBrackets

end Unicode
