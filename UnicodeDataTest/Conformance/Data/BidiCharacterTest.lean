/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeDataTest.Common.Types
import UnicodeDataTest.Common.Parse

namespace UnicodeDataTest.Conformance.Data.BidiCharacterTest

private def parseBidiCharacterTestLine? (lineNo : Nat) (raw : String) : Option UnicodeDataTest.BidiCharacterTestCase := do
  let line := Unicode.UCD.trimAsciiString raw
  if line.isEmpty || line.startsWith "#" then
    none
  else
    let (body, comment) := UnicodeDataTest.Common.Parse.splitComment line
    let cols := body.splitOn ";" |>.toArray.map Unicode.UCD.trimAsciiString
    if cols.size < 5 then
      none
    else
      some {
        line := lineNo
        input := Unicode.UCD.parseCodePointSequenceField cols[0]!.toSlice
        paragraphDirection := UnicodeDataTest.Common.Parse.parseBidiParagraphDirection cols[1]!
        paragraphLevel := UnicodeDataTest.Common.Parse.parseNat! cols[2]!
        resolvedLevels := UnicodeDataTest.Common.Parse.parseOptNatArray cols[3]!
        visualOrder := UnicodeDataTest.Common.Parse.parseNatArray cols[4]!
        comment := comment
      }

private def parseBidiCharacterTestFile (src : String) : Array UnicodeDataTest.BidiCharacterTestCase :=
  UnicodeDataTest.Common.Parse.parseLines src parseBidiCharacterTestLine?

public def path : String := "data/ucd/conformance/BidiCharacterTest.txt"

public def load : IO (Array UnicodeDataTest.BidiCharacterTestCase) := do
  return parseBidiCharacterTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Conformance.Data.BidiCharacterTest
