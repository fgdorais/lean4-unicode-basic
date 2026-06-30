/-
Copyright © 2025-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedEastAsianWidth.txt` -/
def EastAsianWidth.txt := include_str "../data/ucd/extracted/DerivedEastAsianWidth.txt"

/-- Parsed `EastAsianWidth.txt` records. -/
public def EastAsianWidth.data : Array (UInt32 × UInt32 × EastAsianWidth) :=
  UCD.parseRangeTable EastAsianWidth.txt fun parts => EastAsianWidth.ofAbbrev! parts[1]!

/-- Find the East Asian width for a code point, if it is explicitly listed. -/
public def lookupEastAsianWidth? (code : UInt32) : Option EastAsianWidth :=
  UCD.lookupRange? code EastAsianWidth.data

/-- Find the East Asian width for a code point, defaulting to `N`. -/
public def lookupEastAsianWidth (code : UInt32) : EastAsianWidth :=
  lookupEastAsianWidth? code |>.getD .neutral

end Unicode
