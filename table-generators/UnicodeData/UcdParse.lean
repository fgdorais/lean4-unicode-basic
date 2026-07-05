/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex

namespace Unicode
namespace UCD

/-- Trim ASCII whitespace from a string and materialize a `String`. -/
public def trimAsciiString (s : String) : String := (String.trimAscii s).copy

/-- Trim ASCII whitespace from a string slice and materialize a `String`. -/
public def trimAsciiSlice (s : String.Slice) : String := (String.Slice.trimAscii s).copy

/-- Strip trailing comments from a UCD line. -/
public def stripComment (s : String) : String :=
  trimAsciiSlice <| String.takeWhile s fun c => c != '#'

/-- Parse a hex range field. -/
public def parseRangeField (s : String) : UInt32 × UInt32 :=
  match (trimAsciiString s).splitOn ".." with
  | [c] => (ofHexString! c, ofHexString! c)
  | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
  | _ => panic! "invalid range in UCD file"

/-- Parse a `U+...` code point field. -/
public def parseUPlusField (s : String.Slice) : UInt32 :=
  let s := (String.Slice.trimAscii s).copy
  let s := if s.take 2 == "U+" then s.drop 2 else s
  ofHexString! s

/-- Parse a space-separated code point sequence field. -/
public def parseCodePointSequenceField (s : String.Slice) : Array UInt32 :=
  let s := (String.Slice.trimAscii s).copy
  if s.isEmpty then
    #[]
  else
    s.splitOn " " |>.filter (· ≠ "") |>.map (fun x => ofHexString! x.toSlice) |>.toArray

/-- Parse a range table with a value parser. -/
public def parseRangeTable {α} (s : String) (parseValue : Array String → α) :
    Array (UInt32 × UInt32 × α) := Id.run do
  let mut data := #[]
  for raw in s.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";" |>.toArray.map trimAsciiString
      let (c₀, c₁) := parseRangeField parts[0]!
      data := data.push (c₀, c₁, parseValue parts)
  return data.qsort fun a b => a.1 < b.1

/-- Parse a range table and collect `# @missing:` directives too. -/
public def parseRangeTableWithMissing {α} (s : String) (parseValue : Array String → α) :
    Array (UInt32 × UInt32 × α) × Array (UInt32 × UInt32 × α) := Id.run do
  let mut explicit := #[]
  let mut missing := #[]
  for raw in s.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      if line.startsWith "# @missing:" then
        let body := trimAsciiSlice <| line.drop "# @missing:".length
        let parts := body.splitOn ";" |>.toArray.map trimAsciiString
        let (c₀, c₁) := parseRangeField parts[0]!
        missing := missing.push (c₀, c₁, parseValue parts)
      else
        continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";" |>.toArray.map trimAsciiString
      let (c₀, c₁) := parseRangeField parts[0]!
      explicit := explicit.push (c₀, c₁, parseValue parts)
  return (explicit.qsort fun a b => a.1 < b.1, missing.qsort fun a b => a.1 < b.1)

/-- Binary-search a sorted range table. -/
public partial def lookupRange? {α} (code : UInt32) (data : Array (UInt32 × UInt32 × α)) :
    Option α :=
  let rec go (lo hi : Nat) : Option α :=
    if _ : lo < hi then
      let mid := lo + (hi - lo) / 2
      match data[mid]? with
      | some (c₀, c₁, v) =>
        if code < c₀ then
          go lo mid
        else if c₁ < code then
          go (mid + 1) hi
        else
          some v
      | none => none
    else
      none
  go 0 data.size

end UCD
end Unicode
