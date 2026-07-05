/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedBinaryProperties.txt` -/
def DerivedBinaryProperties.txt := include_str "../../data-ucd/extracted/DerivedBinaryProperties.txt"

private def DerivedBinaryProperties.table : Array (UInt32 × UInt32 × Unit) :=
  UCD.parseRangeTable DerivedBinaryProperties.txt fun _ => ()

/-- Parsed `Bidi_Mirrored` ranges. -/
public def DerivedBinaryProperties.bidiMirrored : Array (UInt32 × UInt32) :=
  DerivedBinaryProperties.table.map fun x => (x.1, x.2.1)

/-- Check whether a code point has `Bidi_Mirrored`. -/
public def lookupDerivedBidiMirrored (code : UInt32) : Bool :=
  match UCD.lookupRange? code DerivedBinaryProperties.table with
  | some _ => true
  | none => false

end Unicode
