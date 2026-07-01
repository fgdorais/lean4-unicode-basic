/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi

open Unicode

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

/-- Parsed `BidiTest.txt` row. -/
public structure BidiTestCase where
  line : Nat
  expectedLevels : Array (Option Nat)
  expectedReorder : Array Nat
  input : Array BidiClass
  paragraphMask : Nat
  comment : Option String := none
deriving Inhabited, Repr

end UnicodeDataTest
