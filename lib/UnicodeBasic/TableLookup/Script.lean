/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.MaybeUnknownScript
public import UnicodeBasicCommon.Types.Script
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Script

namespace Unicode

/-- Get the script of a code point using lookup table

  Unicode property: `Script` -/
@[inline]
public def lookupScript (c : UInt32) : MaybeUnknownScript :=
  if h : TableLookupTables.Script.BetweenOrEqStartEnd c then
    (TableLookupTables.Script.getInsideSparseRangeValueTable c h).elim default MaybeUnknownScript.ofScript
  else
    default
