/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `HangulSyllableType.txt` -/
def HangulSyllableType.txt := include_str "../../data-ucd/core/HangulSyllableType.txt"

/-- Parsed `HangulSyllableType.txt` data and defaults. -/
public def HangulSyllableType.data : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing HangulSyllableType.txt fun parts => UCD.trimAsciiSlice parts[1]!).1

/-- Parsed `HangulSyllableType.txt` defaults. -/
private def HangulSyllableType.defaults : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing HangulSyllableType.txt fun parts => UCD.trimAsciiSlice parts[1]!).2

/-- Find the Hangul syllable type for a code point, if explicitly listed. -/
public def lookupHangulSyllableType? (code : UInt32) : Option String :=
  match UCD.lookupRange? code HangulSyllableType.data with
  | some v => some v
  | none => UCD.lookupRange? code HangulSyllableType.defaults

/-- Find the Hangul syllable type for a code point, defaulting to `Not_Applicable`. -/
public def lookupHangulSyllableType (code : UInt32) : String :=
  lookupHangulSyllableType? code |>.getD "Not_Applicable"

end Unicode
