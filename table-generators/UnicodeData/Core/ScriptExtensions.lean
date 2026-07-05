/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Std.Data.HashMap
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Type for script extensions data -/
public abbrev ScriptExtensions := Std.HashMap String.Slice (Array (UInt32 × UInt32))

/-- Raw string from `ScriptExtensions.txt` -/
public def ScriptExtensions.txt := include_str "../../data-ucd/core/ScriptExtensions.txt"

public initialize ScriptExtensions.data : ScriptExtensions ← do
  let stream := UCDStream.ofString ScriptExtensions.txt
  let mut t : ScriptExtensions := {}
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in ScriptExtensions.txt"
    let scripts := record[1]!.split " "
    for sc in scripts do
      if sc.isEmpty then continue
      match t.get? sc with
      | some a =>
        let (d₀, d₁) := a.back!
        if c₀ = d₁ + 1 then
          t := t.insert sc (a.pop.push (d₀, c₁))
        else
          t := t.insert sc (a.push (c₀, c₁))
      | none =>
        t := t.insert sc #[(c₀, c₁)]
  return t

/-- Get table for given script extension -/
@[inline]
public def ScriptExtensions.getTable? (sc : String.Slice) : Option <| Array (UInt32 × UInt32) :=
  data.get? sc

@[inline, inherit_doc ScriptExtensions.getTable?]
public def ScriptExtensions.getTable! (sc : String.Slice) : Array (UInt32 × UInt32) :=
  getTable? sc |>.get!

end Unicode
