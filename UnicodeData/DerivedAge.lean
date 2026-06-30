/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedAge.txt` -/
def DerivedAge.txt := include_str "../data/ucd/core/DerivedAge.txt"

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
  | _ => panic! "invalid range in DerivedAge.txt"

/-- Parsed `DerivedAge.txt` records and defaults. -/
public def DerivedAge.data : Array (UInt32 × UInt32 × String) := Id.run do
  let mut explicit := #[]
  let mut defaults := #[]
  for raw in DerivedAge.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      if line.startsWith "# @missing:" then
        let body := trimAsciiSlice <| line.drop "# @missing:".length
        let parts := body.splitOn ";"
        let (c₀, c₁) := parseRangeField parts[0]!
        let age := trimAsciiSlice parts[1]!
        defaults := defaults.push (c₀, c₁, age)
      else
        continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let age := trimAsciiSlice parts[1]!
      explicit := explicit.push (c₀, c₁, age)
  return explicit.qsort fun a b => a.1.1 < b.1.1

private def DerivedAge.defaults : Array (UInt32 × UInt32 × String) := Id.run do
  let mut defaults := #[]
  for raw in DerivedAge.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.startsWith "# @missing:" then
      let body := trimAsciiSlice <| line.drop "# @missing:".length
      let parts := body.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let age := trimAsciiSlice parts[1]!
      defaults := defaults.push (c₀, c₁, age)
  return defaults.qsort fun a b => a.1.1 < b.1.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × String)) (lo hi : Nat) : Option String :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, age) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some age
  else
    none

/-- Find the age for a code point, if explicitly listed. -/
public def lookupDerivedAge? (code : UInt32) : Option String :=
  match find code DerivedAge.data 0 DerivedAge.data.size with
  | some age => some age
  | none => find code DerivedAge.defaults 0 DerivedAge.defaults.size

/-- Find the age for a code point, defaulting to `NA`. -/
public def lookupDerivedAge (code : UInt32) : String :=
  lookupDerivedAge? code |>.getD "NA"

end Unicode
