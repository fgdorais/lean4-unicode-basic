/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedAge.txt` -/
def DerivedAge.txt := include_str "../../data-ucd/core/DerivedAge.txt"

/-- Parsed `DerivedAge.txt` records and defaults. -/
public def DerivedAge.data : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing DerivedAge.txt fun parts => UCD.trimAsciiSlice parts[1]!).1

private def DerivedAge.defaults : Array (UInt32 × UInt32 × String) :=
  (UCD.parseRangeTableWithMissing DerivedAge.txt fun parts => UCD.trimAsciiSlice parts[1]!).2

/-- Find the age for a code point, if explicitly listed. -/
public def lookupDerivedAge? (code : UInt32) : Option String :=
  match UCD.lookupRange? code DerivedAge.data with
  | some age => some age
  | none => UCD.lookupRange? code DerivedAge.defaults

/-- Find the age for a code point, defaulting to `NA`. -/
public def lookupDerivedAge (code : UInt32) : String :=
  lookupDerivedAge? code |>.getD "NA"

end Unicode
