/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types.WordBreak
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.WordBreak

namespace Unicode

/-- Get word break property using lookup table -/
public def lookupWordBreak (c : UInt32) : MaybeWordBreak :=
  if h : TableLookupTables.WordBreak.BetweenOrEqStartEnd c then
    (TableLookupTables.WordBreak.getInsideSparseRangeValueTable c h).elim .other .nonOther
  else
    .other
