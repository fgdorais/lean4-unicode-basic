/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeDataTest.Common.Parse
public import UnicodeBasic.Bidi

namespace UnicodeDataTest.Conformance.Data.BidiTest

open Unicode

public def parseBidiInput (s : String) : Array BidiClass :=
  let s := UCD.trimAsciiString s
  if s.isEmpty then
    #[]
  else
    s.splitOn " " |>.toArray.filter (· ≠ "") |>.map fun x => BidiClass.ofAbbrev! x.toSlice

/-- Parsed `BidiTest.txt` row. -/
public structure BidiTestCase where
  line : Nat
  expectedLevels : Array (Option Nat)
  expectedReorder : Array Nat
  input : Array BidiClass
  paragraphMask : Nat
  comment : Option String := none
deriving Inhabited --, Repr

private def parseBidiTestFile (src : String) : Array BidiTestCase :=
  Id.run do
    let mut levels : Array (Option Nat) := #[]
    let mut reorder : Array Nat := #[]
    let mut out := #[]
    let mut lineNo := 0
    for row in src.splitOn "\n" do
      lineNo := lineNo + 1
      let line := Unicode.UCD.trimAsciiString row
      if line.isEmpty || line.startsWith "#" then
        continue
      else if line.startsWith "@Levels:" then
        levels := UnicodeDataTest.Common.Parse.parseOptNatArray ((line.drop "@Levels:".length).copy)
      else if line.startsWith "@Reorder:" then
        reorder := UnicodeDataTest.Common.Parse.parseNatArray ((line.drop "@Reorder:".length).copy)
      else if line.startsWith "@" then
        continue
      else
        let (body, comment) := UnicodeDataTest.Common.Parse.splitComment line
        let cols := body.splitOn ";" |>.toArray.map Unicode.UCD.trimAsciiString
        if cols.size < 2 then
          continue
        out := out.push {
          line := lineNo
          expectedLevels := levels
          expectedReorder := reorder
          input := parseBidiInput cols[0]!
          paragraphMask := UnicodeDataTest.Common.Parse.parseNat! cols[1]!
          comment := comment
        }
    return out

public def path : String := "../table-generators/data-ucd/conformance/BidiTest.txt"

public def load : IO (Array BidiTestCase) := do
  return parseBidiTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Conformance.Data.BidiTest
