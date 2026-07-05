/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Dash

namespace Unicode

/-- Check if code point has Dash property using lookup table -/
public def lookupDash (c : UInt32) : Bool :=
  if h : TableLookupTables.Dash.BetweenOrEqStartEnd c then
    TableLookupTables.Dash.IsInsideSparseRangeTable c h
  else
    false
