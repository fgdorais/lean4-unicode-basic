/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasicCommon.Types.NumericType
public import UnicodeData.Extracted.DerivedNumericType
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedNumericValues.txt` -/
def DerivedNumericValues.txt := include_str "../../data-ucd/extracted/DerivedNumericValues.txt"

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
  | _ => panic! "invalid range in DerivedNumericValues.txt"

/-- Parse a numeric value field. -/
private def parseNumericValueField (s : String) : NumericType :=
  let s := trimAsciiString s
  if s.contains '/' then
    match s.split "/" |>.toStringList with
    | [n, d] => .numeric n.toInt! (some d.toNat!)
    | _ => panic! "invalid numeric value"
  else
    .numeric s.toInt! none

/-- Parsed `DerivedNumericValues.txt` records. -/
public def DerivedNumericValues.data : Array (UInt32 × UInt32 × NumericType) := Id.run do
  let mut data := #[]
  for raw in DerivedNumericValues.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty || line.startsWith "# " then
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      let (c₀, c₁) := parseRangeField parts[0]!
      let n := parseNumericValueField parts[3]!
      data := data.push (c₀, c₁, n)
  return data.qsort fun a b => a.1 < b.1

private partial def find (code : UInt32)
    (data : Array (UInt32 × UInt32 × NumericType)) (lo hi : Nat) : Option NumericType :=
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

/-- Find the numeric value for a code point, if explicitly listed in the derived values file. -/
public def lookupDerivedNumericValue? (code : UInt32) : Option NumericType :=
  if lookupNumericType code then
    find code DerivedNumericValues.data 0 DerivedNumericValues.data.size
  else
    none

/-- Find the numeric value for a code point, defaulting to `none`. -/
public def lookupDerivedNumericValue (code : UInt32) : Option NumericType :=
  lookupDerivedNumericValue? code

end Unicode
