/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Diacritic

namespace Unicode

/-- Check if code point has Diacritic property using lookup table -/
public abbrev lookupDiacritic (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.Diacritic.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.Diacritic.IsInsideSparseRangeTable c h
  else
    False
