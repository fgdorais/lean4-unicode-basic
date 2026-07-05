/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeDataTest.Common.Types
import UnicodeDataTest.Auxiliary.Common

namespace UnicodeDataTest.Auxiliary.Data.LineBreakTest

public def path : String := "../table-generators/data-ucd/auxiliary/LineBreakTest.txt"

public def load : IO (Array UnicodeDataTest.BreakTestCase) := do
  return UnicodeDataTest.Auxiliary.Common.parseBreakTestFile (← IO.FS.readFile path)

end UnicodeDataTest.Auxiliary.Data.LineBreakTest
