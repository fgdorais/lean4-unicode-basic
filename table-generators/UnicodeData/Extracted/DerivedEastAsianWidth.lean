/-
Copyright © 2025-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.EastAsianWidth
import UnicodeData.UcdParse

namespace Unicode

namespace EastAsianWidth

/-- Raw string from `DerivedEastAsianWidth.txt` -/
public def txt := include_str "../../data-ucd/extracted/DerivedEastAsianWidth.txt"

/-- Parsed `EastAsianWidth.txt` records. -/
public def data : Array (UInt32 × UInt32 × EastAsianWidth) :=
  UCD.parseRangeTable txt fun parts => EastAsianWidth.ofAbbrev! parts[1]!

/-- Find the East Asian width for a code point, if it is explicitly listed. -/
public def lookup? (code : UInt32) : Option EastAsianWidth :=
  UCD.lookupRange? code data

/-- Find the East Asian width for a code point, defaulting to `N`. -/
public def lookup (code : UInt32) : EastAsianWidth :=
  lookup? code |>.getD .neutral

end EastAsianWidth

end Unicode
