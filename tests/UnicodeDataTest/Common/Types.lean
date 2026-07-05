/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

namespace UnicodeDataTest

/-- Parsed break-test row used by grapheme/word/sentence/line break fixtures. -/
public structure BreakTestCase where
  /-- Source line in the fixture file. -/
  line : Nat
  /-- Input code points from the test row. -/
  codepoints : Array UInt32
  /-- Expected boundary positions, measured between code points. -/
  boundaries : Array Nat
  /-- Trailing comment, if present. -/
  comment : Option String := none
deriving Inhabited, Repr

end UnicodeDataTest
