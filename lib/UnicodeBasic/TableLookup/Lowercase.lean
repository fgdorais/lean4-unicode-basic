/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Lowercase

namespace Unicode

/-- Check if code point is a lowercase letter using lookup table

  Unicode property: `Lowercase` -/
public abbrev lookupLowercase (c : UInt32) : Prop :=
  if h : TableLookupTables.Lowercase.BetweenOrEqStartEnd c then
    TableLookupTables.Lowercase.IsInsideSparseRangeTable c h
  else
    False
