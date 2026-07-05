/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi
import UnicodeDataTest.Common.Parse

open Unicode

namespace UnicodeDataTest.Conformance.Data.BidiCharacterTest

/-- Parsed `BidiCharacterTest.txt` row. -/
public structure BidiCharacterTestCase where
  line : Nat
  input : Array UInt32
  paragraphDirection : BidiParagraphDirection
  paragraphLevel : Nat
  resolvedLevels : Array (Option Nat)
  visualOrder : Array Nat
  comment : Option String := none
deriving Inhabited, Repr

public def parseBidiParagraphDirection (s : String) : Unicode.BidiParagraphDirection :=
  match UCD.trimAsciiString s with
  | "0" => .ltr
  | "1" => .rtl
  | "2" => .autoLtr
  | _ => panic! s!"invalid bidi paragraph direction: {s}"

private def parseBidiCharacterTestLine? (lineNo : Nat) (raw : String) : Option BidiCharacterTestCase := do
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
        paragraphDirection := parseBidiParagraphDirection cols[1]!
        paragraphLevel := UnicodeDataTest.Common.Parse.parseNat! cols[2]!
        resolvedLevels := UnicodeDataTest.Common.Parse.parseOptNatArray cols[3]!
        visualOrder := UnicodeDataTest.Common.Parse.parseNatArray cols[4]!
        comment := comment
      }

private def parseBidiCharacterTestFile (src : String) : Array BidiCharacterTestCase :=
  UnicodeDataTest.Common.Parse.parseLines src parseBidiCharacterTestLine?

public def path : String := "../table-generators/data-ucd/conformance/BidiCharacterTest.txt"

public def load : IO (Array BidiCharacterTestCase) := do
  return parseBidiCharacterTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Conformance.Data.BidiCharacterTest
