/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Uppercase

namespace Unicode

/-- Check if code point is a uppercase letter using lookup table

  Unicode property: `Uppercase` -/
public abbrev lookupUppercase (c : UInt32) : Prop :=
  if h : TableLookupTables.Uppercase.BetweenOrEqStartEnd c then
    TableLookupTables.Uppercase.IsInsideSparseRangeTable c h
  else
    False
