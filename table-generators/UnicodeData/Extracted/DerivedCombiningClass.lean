/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedCombiningClass.txt` -/
def DerivedCombiningClass.txt := include_str "../../data-ucd/extracted/DerivedCombiningClass.txt"

/-- Parsed non-zero combining class ranges. -/
public def DerivedCombiningClass.data : Array (UInt32 × UInt32 × Nat) :=
  (UCD.parseRangeTable DerivedCombiningClass.txt fun parts => parts[1]!.toNat!).filter fun x =>
    x.2.2 != 0

/-- Find the canonical combining class for a code point, if explicitly listed. -/
public def lookupDerivedCombiningClass? (code : UInt32) : Option Nat :=
  UCD.lookupRange? code DerivedCombiningClass.data

/-- Find the canonical combining class for a code point, defaulting to `0`. -/
public def lookupDerivedCombiningClass (code : UInt32) : Nat :=
  lookupDerivedCombiningClass? code |>.getD 0

end Unicode
