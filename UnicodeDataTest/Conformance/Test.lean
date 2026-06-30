/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeDataTest.Conformance.Data.BidiCharacterTest
import UnicodeDataTest.Conformance.Data.BidiTest
import UnicodeDataTest.Conformance.Data.NormalizationTest
import UnicodeDataTest.Common.Failure
import UnicodeDataTest.Conformance.Normalization

namespace UnicodeDataTest.Conformance

public def run : IO UInt32 := do
  let nt ← UnicodeDataTest.Conformance.Data.NormalizationTest.load
  let bc ← UnicodeDataTest.Conformance.Data.BidiCharacterTest.load
  let bt ← UnicodeDataTest.Conformance.Data.BidiTest.load
  let rc ← UnicodeDataTest.Common.reportFailures "NormalizationTest" <|
    UnicodeDataTest.Conformance.Normalization.runConformance "NormalizationTest.txt" nt
  if !bc.isEmpty then
    IO.eprintln s!"BidiCharacterTest.txt: parsed {bc.size} rows (pending bidi implementation)"
  if !bt.isEmpty then
    IO.eprintln s!"BidiTest.txt: parsed {bt.size} rows (pending bidi implementation)"
  return rc

end UnicodeDataTest.Conformance
