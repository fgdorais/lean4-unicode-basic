/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.HashMap
import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase
import UnicodeData.Aliases

namespace Unicode

/-- Type for scripts data -/
abbrev Scripts := Std.HashMap String.Slice (Array (UInt32 × UInt32))

/-- Raw string from `Scripts.txt` -/
def Scripts.txt := include_str "../data/Scripts.txt"

initialize Scripts.data : Scripts ← do
  let stream := UCDStream.ofString Scripts.txt
  let mut t := {}
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in Scripts.txt"
    match t.get? record[1]! with
    | some a =>
      let (d₀, d₁) := a.back!
      if c₀ = d₁ + 1 then
        t := t.insert record[1]! (a.pop.push (d₀, c₁))
      else
        t := t.insert record[1]! (a.push (c₀, c₁))
    | none =>
      t := t.insert record[1]! #[(c₀, c₁)]
  return t

/-- Get table for given script -/
@[inline]
def Scripts.getTable? (sc : String.Slice) : Option <| Array (UInt32 × UInt32) := do
  let sc ← PropertyValueAliases.getLongName! "Script" sc
  data.get? sc

@[inline, inherit_doc Scripts.getTable?]
def Scripts.getTable! (sc : String.Slice) : Array (UInt32 × UInt32) :=
  getTable? sc |>.get!

end Unicode
