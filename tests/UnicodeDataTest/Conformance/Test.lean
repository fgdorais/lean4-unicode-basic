/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Spec.Tree
import UnicodeDataTest.Conformance.Data.BidiCharacterTest
import UnicodeDataTest.Conformance.Data.BidiTest
import UnicodeDataTest.Conformance.Data.NormalizationTest
import UnicodeDataTest.Common.Failure
import UnicodeDataTest.Conformance.Bidi
import UnicodeDataTest.Conformance.Normalization

namespace UnicodeDataTest.Conformance

public def spec : Spec.Spec := do
  Spec.describe "Conformance" do
    Spec.it "NormalizationTest" do
      let nt ← UnicodeDataTest.Conformance.Data.NormalizationTest.load
      let rc ← UnicodeDataTest.Common.reportFailures "NormalizationTest" <|
        UnicodeDataTest.Conformance.Normalization.runConformance "NormalizationTest.txt" nt
      if rc != 0 then
        Spec.Assert.fail "NormalizationTest failed"

    Spec.it "BidiCharacterTest" do
      let bc ← UnicodeDataTest.Conformance.Data.BidiCharacterTest.load
      let bt ← UnicodeDataTest.Conformance.Data.BidiTest.load
      let bidiFailures := UnicodeDataTest.Conformance.Bidi.runConformance bc bt
      let bcfc ← UnicodeDataTest.Common.reportFailures "BidiCharacterTest" <|
        bidiFailures.filter fun f => f.file == "BidiCharacterTest.txt"
      if bcfc != 0 then
        Spec.Assert.fail "BidiCharacterTest failed"

    Spec.it "BidiTest" do
      let bc ← UnicodeDataTest.Conformance.Data.BidiCharacterTest.load
      let bt ← UnicodeDataTest.Conformance.Data.BidiTest.load
      let bidiFailures := UnicodeDataTest.Conformance.Bidi.runConformance bc bt
      let btfc ← UnicodeDataTest.Common.reportFailures "BidiTest" <|
        bidiFailures.filter fun f => f.file == "BidiTest.txt"
      if btfc != 0 then
        Spec.Assert.fail "BidiTest failed"

end UnicodeDataTest.Conformance
