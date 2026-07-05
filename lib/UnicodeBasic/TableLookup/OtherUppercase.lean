/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.OtherUppercase

namespace Unicode

/-- Check if code point has Other_Uppercase property using lookup table -/
public abbrev lookupOtherUppercase (c : UInt32) : Prop :=
  if h : TableLookupTables.OtherUppercase.BetweenOrEqStartEnd c then
    TableLookupTables.OtherUppercase.IsInsideSparseRangeTable c h
  else
    False
