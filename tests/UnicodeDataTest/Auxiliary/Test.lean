/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Spec.Tree
import UnicodeBasic
import UnicodeDataTest.Auxiliary.Grapheme
import UnicodeDataTest.Auxiliary.Data.GraphemeBreakTest
import UnicodeDataTest.Auxiliary.Data.LineBreakTest
import UnicodeDataTest.Auxiliary.Data.SentenceBreakTest
import UnicodeDataTest.Auxiliary.Data.WordBreakTest
import UnicodeDataTest.Common.Failure

namespace UnicodeDataTest.Auxiliary

private def ensureNonEmpty (name : String) (cases : Array UnicodeDataTest.BreakTestCase) : IO UInt32 := do
  if cases.isEmpty then
    IO.eprintln s!"{name}: parsed no test cases"
    return 1
  else
    return 0

private def reportPendingAlgorithm (name : String) (cases : Array UnicodeDataTest.BreakTestCase) : IO UInt32 := do
  let rc ← ensureNonEmpty name cases
  if rc == 0 then
    IO.eprintln s!"{name}: parsed {cases.size} rows (pending segmentation implementation)"
  return rc

private def runBoundaries
    (file : String)
    (cases : Array UnicodeDataTest.BreakTestCase)
    (segment : Array UInt32 → Array Nat) :
    Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  for tc in cases do
    let actual := segment tc.codepoints
    if actual != tc.boundaries then
      failures := failures.push {
        file := file
        line := tc.line
        expected := s!"{tc.boundaries}"
        actual := s!"{actual}"
        comment := tc.comment
      }
  return failures

public def spec : Spec.Spec := do
  Spec.describe "Auxiliary" do
    Spec.it "GraphemeBreakTest" do
      let g ← UnicodeDataTest.Auxiliary.Data.GraphemeBreakTest.load
      let rc ← UnicodeDataTest.Common.reportFailures "GraphemeBreakTest" <|
        UnicodeDataTest.Auxiliary.Grapheme.runConformance "GraphemeBreakTest.txt" g
      if rc != 0 then
        Spec.Assert.fail "GraphemeBreakTest failed"

    Spec.it "WordBreakTest" do
      let w ← UnicodeDataTest.Auxiliary.Data.WordBreakTest.load
      let wc ← UnicodeDataTest.Common.reportFailures "WordBreakTest" <|
        runBoundaries "WordBreakTest.txt" w Unicode.segmentWordBoundaries
      if wc != 0 then
        Spec.Assert.fail "WordBreakTest failed"

    Spec.it "SentenceBreakTest" do
      let s ← UnicodeDataTest.Auxiliary.Data.SentenceBreakTest.load
      let sc ← UnicodeDataTest.Common.reportFailures "SentenceBreakTest" <|
        runBoundaries "SentenceBreakTest.txt" s Unicode.segmentSentenceBoundaries
      if sc != 0 then
        Spec.Assert.fail "SentenceBreakTest failed"

    Spec.it "LineBreakTest" do
      let l ← UnicodeDataTest.Auxiliary.Data.LineBreakTest.load
      let lc ← UnicodeDataTest.Common.reportFailures "LineBreakTest" <|
        runBoundaries "LineBreakTest.txt" l Unicode.segmentLineBoundaries
      if lc != 0 then
        Spec.Assert.fail "LineBreakTest failed"

end UnicodeDataTest.Auxiliary
