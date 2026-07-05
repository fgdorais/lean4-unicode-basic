/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.OtherAlphabetic

namespace Unicode

/-- Check if code point has Other_Alphabetic property using lookup table -/
public abbrev lookupOtherAlphabetic (c : UInt32) : Prop :=
  if h : TableLookupTables.OtherAlphabetic.BetweenOrEqStartEnd c then
    TableLookupTables.OtherAlphabetic.IsInsideSparseRangeTable c h
  else
    False
