/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.GeneralCategory
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.GeneralCategory

namespace Unicode

/-- Get general category of a code point using lookup table

  Unicode property: `General_Category` -/
@[inline]
public def lookupGC (c : UInt32) : GC :=
  if h : TableLookupTables.GeneralCategory.BetweenOrEqStartEnd c then
    match TableLookupTables.GeneralCategory.getInsideSparseRangeValueTable c h with
    | some raw => decodeGeneralCategory c raw
    -- `GC.Cn` = "Unassigned" (Not Assigned): the default category for any code
    -- point that does not appear in the Unicode Character Database, i.e. gaps
    -- between assigned ranges in the lookup table return `none`.
    | none => GC.Cn
  else
    -- Code point is outside the table's covered range [start, end]; by Unicode
    -- convention all such points are also unassigned (`Cn`).
    GC.Cn
