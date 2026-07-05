/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Cased

namespace Unicode

/-- Check if code point is a cased letter using lookup table

  Unicode property: `Cased` -/
@[inline]
public def lookupCased (c : UInt32 ) : Bool :=
  if h : TableLookupTables.Cased.BetweenOrEqStartEnd c then
    TableLookupTables.Cased.IsInsideSparseRangeTable c h
  else
    false
