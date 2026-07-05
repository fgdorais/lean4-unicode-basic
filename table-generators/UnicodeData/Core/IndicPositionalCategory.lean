/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `IndicPositionalCategory.txt` -/
def IndicPositionalCategory.txt := include_str "../../data-ucd/core/IndicPositionalCategory.txt"

/-- Parsed `IndicPositionalCategory.txt` data and defaults. -/
public def IndicPositionalCategory.data : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing IndicPositionalCategory.txt fun parts => UCD.trimAsciiSlice parts[1]!).1

/-- Parsed `IndicPositionalCategory.txt` defaults. -/
private def IndicPositionalCategory.defaults : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing IndicPositionalCategory.txt fun parts => UCD.trimAsciiSlice parts[1]!).2

/-- Find the Indic positional category for a code point, if explicitly listed. -/
public def lookupIndicPositionalCategory? (code : UInt32) : Option String :=
  match UCD.lookupRange? code IndicPositionalCategory.data with
  | some v => some v
  | none => UCD.lookupRange? code IndicPositionalCategory.defaults

/-- Find the Indic positional category for a code point, defaulting to `Not_Applicable`. -/
public def lookupIndicPositionalCategory (code : UInt32) : String :=
  lookupIndicPositionalCategory? code |>.getD "Not_Applicable"

end Unicode
