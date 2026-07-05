/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.OtherMath

namespace Unicode

/-- Check if code point has Other_Math property using lookup table -/
public abbrev lookupOtherMath (c : UInt32) : Prop :=
  if h : TableLookupTables.OtherMath.BetweenOrEqStartEnd c then
    TableLookupTables.OtherMath.IsInsideSparseRangeTable c h
  else
    False
