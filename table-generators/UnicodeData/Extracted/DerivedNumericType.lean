/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedNumericType.txt` -/
def DerivedNumericType.txt := include_str "../../data-ucd/extracted/DerivedNumericType.txt"

private def DerivedNumericType.table : Array (UInt32 × UInt32 × Unit) :=
  UCD.parseRangeTable DerivedNumericType.txt fun _ => ()

/-- Parsed numeric-type ranges. -/
public def DerivedNumericType.data : Array (UInt32 × UInt32) :=
  DerivedNumericType.table.map fun x => (x.1, x.2.1)

/-- Check whether a code point has `Numeric_Type=Numeric`. -/
public def lookupNumericType (code : UInt32) : Bool :=
  match UCD.lookupRange? code DerivedNumericType.table with
  | some _ => true
  | none => false

end Unicode
