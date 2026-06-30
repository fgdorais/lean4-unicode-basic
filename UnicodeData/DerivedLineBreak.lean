/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData.Aliases
public import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedLineBreak.txt` -/
def DerivedLineBreak.txt := include_str "../data/ucd/extracted/DerivedLineBreak.txt"

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
  | _ => panic! "invalid range in DerivedLineBreak.txt"

/-- Parse a line break field. -/
private def parseLineBreakField (s : String) : LineBreak :=
  let s := trimAsciiString s
  let short :=
    (PropertyValueAliases.getShortName? "lb" s.toSlice).map (fun x => x.copy) |>.getD s
  LineBreak.ofAbbrev! short.toSlice

/-- Parsed `DerivedLineBreak.txt` records and defaults. -/
public def DerivedLineBreak.data : Array (UInt32 × UInt32 × LineBreak) := Id.run do
  let mut explicit := #[]
  let mut defaults := #[]
  for raw in DerivedLineBreak.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      if line.startsWith "# @missing:" then
        let body := trimAsciiSlice <| line.drop "# @missing:".length
        let parts := body.splitOn ";"
        let (c₀, c₁) := parseRangeField parts[0]!
        let lb := parseLineBreakField parts[1]!
        defaults := defaults.push (c₀, c₁, lb)
      else
        continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let lb := parseLineBreakField parts[1]!
      explicit := explicit.push (c₀, c₁, lb)
  return explicit.qsort fun a b => a.1.1 < b.1.1

private def DerivedLineBreak.defaults : Array (UInt32 × UInt32 × LineBreak) := Id.run do
  let mut defaults := #[]
  for raw in DerivedLineBreak.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.startsWith "# @missing:" then
      let body := trimAsciiSlice <| line.drop "# @missing:".length
      let parts := body.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let lb := parseLineBreakField parts[1]!
      defaults := defaults.push (c₀, c₁, lb)
  return defaults.qsort fun a b => a.1.1 < b.1.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × LineBreak)) (lo hi : Nat) : Option LineBreak :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, lb) := data[mid]!
    if code < c₀ then
      find code data lo mid
    else if c₁ < code then
      find code data (mid + 1) hi
    else
      some lb
  else
    none

/-- Find the line break property for a code point, if explicitly listed. -/
public def lookupDerivedLineBreak? (code : UInt32) : Option LineBreak :=
  match find code DerivedLineBreak.data 0 DerivedLineBreak.data.size with
  | some lb => some lb
  | none => find code DerivedLineBreak.defaults 0 DerivedLineBreak.defaults.size

/-- Find the line break property for a code point, defaulting to `Unknown`. -/
public def lookupDerivedLineBreak (code : UInt32) : LineBreak :=
  lookupDerivedLineBreak? code |>.getD .unknown

end Unicode
