/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedJoiningType.txt` -/
def DerivedJoiningType.txt := include_str "../../data-ucd/extracted/DerivedJoiningType.txt"

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
  | _ => panic! "invalid range in DerivedJoiningType.txt"

/-- Parse a joining type field. -/
private def parseJoiningTypeField (s : String) : String :=
  trimAsciiSlice s

/-- Parsed `DerivedJoiningType.txt` ranges. -/
public def DerivedJoiningType.data : Array (UInt32 × UInt32 × String) := Id.run do
  let mut data := #[]
  for raw in DerivedJoiningType.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let jt := parseJoiningTypeField parts[1]!
      data := data.push (c₀, c₁, jt)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × String)) (lo hi : Nat) : Option String :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, jt) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some jt
  else
    none

/-- Find the joining type for a code point, if explicitly listed. -/
public def lookupDerivedJoiningType? (code : UInt32) : Option String :=
  find code DerivedJoiningType.data 0 DerivedJoiningType.data.size

/-- Find the joining type for a code point, defaulting to `Non_Joining`. -/
public def lookupDerivedJoiningType (code : UInt32) : String :=
  lookupDerivedJoiningType? code |>.getD "Non_Joining"

end Unicode
