/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedJoiningGroup.txt` -/
def DerivedJoiningGroup.txt := include_str "../../data-ucd/extracted/DerivedJoiningGroup.txt"

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
  | _ => panic! "invalid range in DerivedJoiningGroup.txt"

/-- Parse a joining group field. -/
private def parseJoiningGroupField (s : String) : String :=
  trimAsciiSlice s

/-- Parsed `DerivedJoiningGroup.txt` ranges. -/
public def DerivedJoiningGroup.data : Array (UInt32 × UInt32 × String) := Id.run do
  let mut data := #[]
  for raw in DerivedJoiningGroup.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let jg := parseJoiningGroupField parts[1]!
      data := data.push (c₀, c₁, jg)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × String)) (lo hi : Nat) : Option String :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, jg) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some jg
  else
    none

/-- Find the joining group for a code point, if explicitly listed. -/
public def lookupDerivedJoiningGroup? (code : UInt32) : Option String :=
  find code DerivedJoiningGroup.data 0 DerivedJoiningGroup.data.size

/-- Find the joining group for a code point, defaulting to `No_Joining_Group`. -/
public def lookupDerivedJoiningGroup (code : UInt32) : String :=
  lookupDerivedJoiningGroup? code |>.getD "No_Joining_Group"

end Unicode
