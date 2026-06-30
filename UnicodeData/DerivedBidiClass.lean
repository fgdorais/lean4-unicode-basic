/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData.Aliases
public import UnicodeBasic.Types

namespace Unicode

/-- Raw string from `DerivedBidiClass.txt` -/
def DerivedBidiClass.txt := include_str "../data/ucd/extracted/DerivedBidiClass.txt"

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
  | _ => panic! "invalid range in DerivedBidiClass.txt"

/-- Parse a bidi class field. -/
private def parseBidiClassField (s : String) : BidiClass :=
  let s := trimAsciiString s
  let short :=
    (PropertyValueAliases.getShortName? "bc" s.toSlice).map (fun x => x.copy) |>.getD s
  BidiClass.ofAbbrev! short.toSlice

/-- Parsed `DerivedBidiClass.txt` records and defaults. -/
public def DerivedBidiClass.data : Array (UInt32 × UInt32 × BidiClass) := Id.run do
  let mut explicit := #[]
  let mut defaults := #[]
  for raw in DerivedBidiClass.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      if line.startsWith "# @missing:" then
        let body := trimAsciiSlice <| line.drop "# @missing:".length
        let parts := body.splitOn ";"
        let (c₀, c₁) := parseRangeField parts[0]!
        let bc := parseBidiClassField parts[1]!
        defaults := defaults.push (c₀, c₁, bc)
      else
        continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let bc := parseBidiClassField parts[1]!
      explicit := explicit.push (c₀, c₁, bc)
  return explicit.qsort fun a b => a.1.1 < b.1.1

private def DerivedBidiClass.defaults : Array (UInt32 × UInt32 × BidiClass) := Id.run do
  let mut defaults := #[]
  for raw in DerivedBidiClass.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.startsWith "# @missing:" then
      let body := trimAsciiSlice <| line.drop "# @missing:".length
      let parts := body.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let bc := parseBidiClassField parts[1]!
      defaults := defaults.push (c₀, c₁, bc)
  return defaults.qsort fun a b => a.1.1 < b.1.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × BidiClass)) (lo hi : Nat) : Option BidiClass :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, bc) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some bc
  else
    none

/-- Find the bidi class for a code point, if explicitly listed. -/
public def lookupDerivedBidiClass? (code : UInt32) : Option BidiClass :=
  match find code DerivedBidiClass.data 0 DerivedBidiClass.data.size with
  | some bc => some bc
  | none => find code DerivedBidiClass.defaults 0 DerivedBidiClass.defaults.size

/-- Find the bidi class for a code point, defaulting to `L`. -/
public def lookupDerivedBidiClass (code : UInt32) : BidiClass :=
  lookupDerivedBidiClass? code |>.getD .L

end Unicode
