/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeDataTest.Conformance.Data.BidiCharacterTest
import UnicodeDataTest.Conformance.Data.BidiTest
import UnicodeDataTest.Conformance.Data.NormalizationTest
import UnicodeDataTest.Common.Failure
import UnicodeDataTest.Conformance.Bidi
import UnicodeDataTest.Conformance.Normalization

namespace UnicodeDataTest.Conformance

public def run : IO UInt32 := do
  let nt ← UnicodeDataTest.Conformance.Data.NormalizationTest.load
  let bc ← UnicodeDataTest.Conformance.Data.BidiCharacterTest.load
  let bt ← UnicodeDataTest.Conformance.Data.BidiTest.load
  let rc ← UnicodeDataTest.Common.reportFailures "NormalizationTest" <|
    UnicodeDataTest.Conformance.Normalization.runConformance "NormalizationTest.txt" nt
  let bidiFailures := UnicodeDataTest.Conformance.Bidi.runConformance bc bt
  let bcfc ← UnicodeDataTest.Common.reportFailures "BidiCharacterTest" <|
    bidiFailures.filter fun f => f.file == "BidiCharacterTest.txt"
  let btfc ← UnicodeDataTest.Common.reportFailures "BidiTest" <|
    bidiFailures.filter fun f => f.file == "BidiTest.txt"
  return if rc == 0 && bcfc == 0 && btfc == 0 then 0 else 1

end UnicodeDataTest.Conformance
