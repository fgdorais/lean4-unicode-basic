/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeDataTest.Common.Types
import UnicodeDataTest.Common.Parse

namespace UnicodeDataTest.Auxiliary.Common

private def parseBreakTestLine? (lineNo : Nat) (raw : String) : Option UnicodeDataTest.BreakTestCase := do
  let line := Unicode.UCD.trimAsciiString raw
  if line.isEmpty || line.startsWith "#" then
    none
  else
    let (body, comment) := UnicodeDataTest.Common.Parse.splitComment line
    let tokens := body.splitOn " " |>.toArray.filter (· ≠ "")
    let mut codepoints := #[]
    let mut boundaries := #[]
    for tok in tokens do
      if tok == "÷" then
        boundaries := boundaries.push codepoints.size
      else if tok == "×" then
        continue
      else
        codepoints := codepoints.push (UnicodeDataTest.Common.Parse.parseHex! tok)
    some {
      line := lineNo
      codepoints := codepoints
      boundaries := boundaries
      comment := comment
    }

public def parseBreakTestFile (src : String) : Array UnicodeDataTest.BreakTestCase :=
  UnicodeDataTest.Common.Parse.parseLines src parseBreakTestLine?

end UnicodeDataTest.Auxiliary.Common
