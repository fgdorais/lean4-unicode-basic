/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.ExtendedPictographic

namespace Unicode

/-- Check if code point has Extended_Pictographic property using lookup table -/
public abbrev lookupExtendedPictographic (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.ExtendedPictographic.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.ExtendedPictographic.IsInsideSparseRangeTable c h
  else
    False
