/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Math

namespace Unicode

/-- Check if code point is a mathematical symbol using lookup table

  Unicode property: `Math` -/
public abbrev lookupMath (c : UInt32) : Prop :=
  if h : TableLookupTables.Math.BetweenOrEqStartEnd c then
    TableLookupTables.Math.IsInsideSparseRangeTable c h
  else
    False
