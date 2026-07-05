/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedName.txt` -/
def DerivedName.txt := include_str "../../data-ucd/extracted/DerivedName.txt"

/-- Trim ASCII whitespace from a string and materialize a `String`. -/
private def trimAsciiString (s : String) : String := (String.trimAscii s).copy

/-- Trim ASCII whitespace from a string slice and materialize a `String`. -/
private def trimAsciiSlice (s : String.Slice) : String := (String.Slice.trimAscii s).copy

/-- Strip trailing comments from a UCD line. -/
private def stripComment (s : String) : String :=
  trimAsciiSlice <| String.takeWhile s fun c => c != '#'

/-- Parse a hex range field. -/
private def parseRangeField (s : String) : UInt32 × UInt32 :=
  match (trimAsciiString s).splitOn ".." with
  | [c] => (ofHexString! c, ofHexString! c)
  | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
  | _ => panic! "invalid range in DerivedName.txt"

/-- Parsed `DerivedName.txt` ranges. -/
public def DerivedName.data : Array (UInt32 × UInt32 × String) := Id.run do
  let mut data := #[]
  for raw in DerivedName.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let n := trimAsciiSlice parts[1]!
      data := data.push (c₀, c₁, n)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × String)) (lo hi : Nat) : Option String :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, n) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some n
  else
    none

/-- Replace the `*` pattern with the code point hex value. -/
private def resolvePattern (c : UInt32) (n : String) : String :=
  if n.contains '*' then
    let hex := toHexStringRaw c
    String.intercalate hex (n.splitOn "*")
  else
    n

/-- Find the derived name for a code point, if explicitly listed. -/
public def lookupDerivedName? (code : UInt32) : Option String :=
  match find code DerivedName.data 0 DerivedName.data.size with
  | some n => some <| resolvePattern code n
  | none => none

/-- Find the derived name for a code point, defaulting to `none`. -/
public noncomputable def lookupDerivedName (code : UInt32) : Option String :=
  lookupDerivedName? code

end Unicode
