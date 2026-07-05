/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData.Core.PropertyValueAliases
public import UnicodeBasicCommon.Types.LineBreak
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `DerivedLineBreak.txt` -/
def DerivedLineBreak.txt := include_str "../../data-ucd/extracted/DerivedLineBreak.txt"

/-- Parse a line break field. -/
private def parseLineBreakField (s : String) : LineBreak :=
  let s := UCD.trimAsciiString s
  let short :=
    (PropertyValueAliases.getShortName? "lb" s.toSlice).map (fun x => x.copy) |>.getD s
  LineBreak.ofAbbrev! short.toSlice

/-- Parsed `DerivedLineBreak.txt` records and defaults. -/
public def DerivedLineBreak.data : Array (UInt32 × UInt32 × LineBreak) :=
  (UCD.parseRangeTableWithMissing DerivedLineBreak.txt fun parts =>
    parseLineBreakField parts[1]! ).1

private def DerivedLineBreak.defaults : Array (UInt32 × UInt32 × LineBreak) :=
  (UCD.parseRangeTableWithMissing DerivedLineBreak.txt fun parts =>
    parseLineBreakField parts[1]! ).2

/-- Find the line break property for a code point, if explicitly listed. -/
public def lookupDerivedLineBreak? (code : UInt32) : Option LineBreak :=
  match UCD.lookupRange? code DerivedLineBreak.data with
  | some lb => some lb
  | none => UCD.lookupRange? code DerivedLineBreak.defaults

/-- Find the line break property for a code point, defaulting to `Unknown`. -/
public def lookupDerivedLineBreak (code : UInt32) : LineBreak :=
  lookupDerivedLineBreak? code |>.getD .unknown

end Unicode
