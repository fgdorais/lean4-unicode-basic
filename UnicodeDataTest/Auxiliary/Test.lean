/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeDataTest.Auxiliary.Grapheme
import UnicodeDataTest.Auxiliary.Segmentation
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

public def run : IO UInt32 := do
  let g ← UnicodeDataTest.Auxiliary.Data.GraphemeBreakTest.load
  let w ← UnicodeDataTest.Auxiliary.Data.WordBreakTest.load
  let s ← UnicodeDataTest.Auxiliary.Data.SentenceBreakTest.load
  let l ← UnicodeDataTest.Auxiliary.Data.LineBreakTest.load
  let rc ← UnicodeDataTest.Common.reportFailures "GraphemeBreakTest" <|
    UnicodeDataTest.Auxiliary.Grapheme.runConformance "GraphemeBreakTest.txt" g
  let wc ← UnicodeDataTest.Common.reportFailures "WordBreakTest" <|
    UnicodeDataTest.Auxiliary.Segmentation.runWordConformance "WordBreakTest.txt" w
  let sc ← UnicodeDataTest.Common.reportFailures "SentenceBreakTest" <|
    UnicodeDataTest.Auxiliary.Segmentation.runSentenceConformance "SentenceBreakTest.txt" s
  let mut failed := rc != 0
  failed := failed || wc != 0
  failed := failed || sc != 0
  failed := failed || (← reportPendingAlgorithm "LineBreakTest" l) != 0
  return if failed then 1 else 0

end UnicodeDataTest.Auxiliary
