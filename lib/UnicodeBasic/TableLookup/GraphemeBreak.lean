/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types.GraphemeClusterBreak
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.GraphemeBreak

namespace Unicode

/-- Get grapheme cluster break property using lookup table -/
public def lookupGraphemeClusterBreak (c : UInt32) : MaybeGraphemeClusterBreak :=
  if h : TableLookupTables.GraphemeBreak.BetweenOrEqStartEnd c then
    (TableLookupTables.GraphemeBreak.getInsideSparseRangeValueTable c h).elim .other .nonOther
  else
    .other
