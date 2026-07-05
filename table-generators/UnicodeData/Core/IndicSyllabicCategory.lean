/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `IndicSyllabicCategory.txt` -/
def IndicSyllabicCategory.txt := include_str "../../data-ucd/core/IndicSyllabicCategory.txt"

/-- Parsed `IndicSyllabicCategory.txt` data and defaults. -/
public def IndicSyllabicCategory.data : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing IndicSyllabicCategory.txt fun parts => UCD.trimAsciiSlice parts[1]!).1

/-- Parsed `IndicSyllabicCategory.txt` defaults. -/
private def IndicSyllabicCategory.defaults : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing IndicSyllabicCategory.txt fun parts => UCD.trimAsciiSlice parts[1]!).2

/-- Find the Indic syllabic category for a code point, if explicitly listed. -/
public def lookupIndicSyllabicCategory? (code : UInt32) : Option String :=
  match UCD.lookupRange? code IndicSyllabicCategory.data with
  | some v => some v
  | none => UCD.lookupRange? code IndicSyllabicCategory.defaults

/-- Find the Indic syllabic category for a code point, defaulting to `Other`. -/
public def lookupIndicSyllabicCategory (code : UInt32) : String :=
  lookupIndicSyllabicCategory? code |>.getD "Other"

end Unicode
