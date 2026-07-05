/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedDecompositionType.txt` -/
def DerivedDecompositionType.txt := include_str "../../data-ucd/extracted/DerivedDecompositionType.txt"

private def DerivedDecompositionType.table : Array (UInt32 × UInt32 × Unit) :=
  UCD.parseRangeTable DerivedDecompositionType.txt fun _ => ()

/-- Parsed canonical decomposition type ranges. -/
public def DerivedDecompositionType.data : Array (UInt32 × UInt32) :=
  DerivedDecompositionType.table.map fun x => (x.1, x.2.1)

/-- Check whether the decomposition type is canonical. -/
public def lookupCanonicalDecompositionType (code : UInt32) : Bool :=
  match UCD.lookupRange? code DerivedDecompositionType.table with
  | some _ => true
  | none => false

end Unicode
