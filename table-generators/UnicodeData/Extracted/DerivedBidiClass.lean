/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData.Core.PropertyValueAliases
public import UnicodeBasicCommon.Types.BidiClass
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedBidiClass.txt` -/
def DerivedBidiClass.txt := include_str "../../data-ucd/extracted/DerivedBidiClass.txt"

/-- Parse a bidi class field. -/
private def parseBidiClassField (s : String) : BidiClass :=
  let s := UCD.trimAsciiString s
  let short :=
    (PropertyValueAliases.getShortName? "bc" s.toSlice).map (fun x => x.copy) |>.getD s
  BidiClass.ofAbbrev! short.toSlice

/-- Parsed `DerivedBidiClass.txt` records and defaults. -/
public def DerivedBidiClass.data : Array (UInt32 × UInt32 × BidiClass) :=
  (UCD.parseRangeTableWithMissing DerivedBidiClass.txt fun parts =>
    parseBidiClassField parts[1]! ).1

private def DerivedBidiClass.defaults : Array (UInt32 × UInt32 × BidiClass) :=
  (UCD.parseRangeTableWithMissing DerivedBidiClass.txt fun parts =>
    parseBidiClassField parts[1]! ).2

/-- Find the bidi class for a code point, if explicitly listed. -/
public def lookupDerivedBidiClass? (code : UInt32) : Option BidiClass :=
  match UCD.lookupRange? code DerivedBidiClass.data with
  | some bc => some bc
  | none => UCD.lookupRange? code DerivedBidiClass.defaults

/-- Find the bidi class for a code point, defaulting to `L`. -/
public def lookupDerivedBidiClass (code : UInt32) : BidiClass :=
  lookupDerivedBidiClass? code |>.getD .L

end Unicode
