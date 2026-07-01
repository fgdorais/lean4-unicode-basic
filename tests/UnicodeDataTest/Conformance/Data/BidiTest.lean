/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeDataTest.Common.Types
import UnicodeDataTest.Common.Parse

namespace UnicodeDataTest.Conformance.Data.BidiTest

private def parseBidiTestFile (src : String) : Array UnicodeDataTest.BidiTestCase :=
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
          input := UnicodeDataTest.Common.Parse.parseBidiInput cols[0]!
          paragraphMask := UnicodeDataTest.Common.Parse.parseNat! cols[1]!
          comment := comment
        }
    return out

public def path : String := "data/ucd/conformance/BidiTest.txt"

public def load : IO (Array UnicodeDataTest.BidiTestCase) := do
  return parseBidiTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Conformance.Data.BidiTest
