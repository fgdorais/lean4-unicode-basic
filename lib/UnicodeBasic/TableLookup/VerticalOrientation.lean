/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.VerticalOrientation
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.VerticalOrientation

namespace Unicode

/-- Get vertical orientation for a code point.

  Unicode property: `Vertical_Orientation`
-/
public def lookupVerticalOrientation (c : UInt32) : VerticalOrientation :=
  if h : TableLookupTables.VerticalOrientation.BetweenOrEqStartEnd c then
    (TableLookupTables.VerticalOrientation.getInsideSparseRangeValueTable c h).getD .rotated
  else
    .rotated
