/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeDataTest.Common.Parse

namespace UnicodeDataTest.Conformance.Data.NormalizationTest

/-- Parsed normalization-test row. -/
public structure NormalizationTestCase where
  line : Nat
  source : Array UInt32
  nfc : Array UInt32
  nfd : Array UInt32
  nfkc : Array UInt32
  nfkd : Array UInt32
  comment : Option String := none
deriving Inhabited, Repr

private def parseNormalizationTestLine? (lineNo : Nat) (raw : String) : Option NormalizationTestCase := do
  let line := Unicode.UCD.trimAsciiString raw
  if line.isEmpty || line.startsWith "#" || line.startsWith "@" then
    none
  else
    let (body, comment) := UnicodeDataTest.Common.Parse.splitComment line
    let cols := body.splitOn ";" |>.toArray.map Unicode.UCD.trimAsciiString
    if cols.size < 5 then
      none
    else
      some {
        line := lineNo
        source := Unicode.UCD.parseCodePointSequenceField cols[0]!.toSlice
        nfc := Unicode.UCD.parseCodePointSequenceField cols[1]!.toSlice
        nfd := Unicode.UCD.parseCodePointSequenceField cols[2]!.toSlice
        nfkc := Unicode.UCD.parseCodePointSequenceField cols[3]!.toSlice
        nfkd := Unicode.UCD.parseCodePointSequenceField cols[4]!.toSlice
        comment := comment
      }

private def parseNormalizationTestFile (src : String) : Array NormalizationTestCase :=
  UnicodeDataTest.Common.Parse.parseLines src parseNormalizationTestLine?

public def path : String := "../table-generators/data-ucd/conformance/NormalizationTest.txt"

public def load : IO (Array NormalizationTestCase) := do
  return parseNormalizationTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Conformance.Data.NormalizationTest
