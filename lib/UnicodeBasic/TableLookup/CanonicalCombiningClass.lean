/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.CanonicalCombiningClass

namespace Unicode

/-- Get canonical combining class using lookup table

  Unicode property: `Canonical_Combining_Class` -/
public def lookupCanonicalCombiningClass (c : UInt32) : Nat :=
  if h : TableLookupTables.CanonicalCombiningClass.BetweenOrEqStartEnd c then
    (TableLookupTables.CanonicalCombiningClass.getInsideSparseRangeValueTable c h).getD 0
  else
    0
