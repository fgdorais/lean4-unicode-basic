/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.GeneralCategory
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedGeneralCategory.txt` -/
def DerivedGeneralCategory.txt := include_str "../../data-ucd/extracted/DerivedGeneralCategory.txt"

/-- Parsed `DerivedGeneralCategory.txt` ranges. -/
public def DerivedGeneralCategory.data : Array (UInt32 × UInt32 × GC) :=
  UCD.parseRangeTable DerivedGeneralCategory.txt fun parts => GC.ofAbbrev! parts[1]!

/-- Find the general category for a code point, if explicitly listed. -/
public def lookupDerivedGeneralCategory? (code : UInt32) : Option GC :=
  UCD.lookupRange? code DerivedGeneralCategory.data

/-- Find the general category for a code point, defaulting to `Cn`. -/
public def lookupDerivedGeneralCategory (code : UInt32) : GC :=
  lookupDerivedGeneralCategory? code |>.getD .Cn

end Unicode
