/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.EastAsianWidth
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.EastAsianWidth

namespace Unicode

/-- Get East Asian width for a code point.

  Unicode property: `East_Asian_Width`
-/
public def lookupEastAsianWidth (c : UInt32) : EastAsianWidth :=
  if h : TableLookupTables.EastAsianWidth.BetweenOrEqStartEnd c then
    match TableLookupTables.EastAsianWidth.getInsideSparseRangeValueTable c h with
    | some w => w
    | none => .neutral
  else
    .neutral
