/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.BlockName
public import UnicodeBasic.Types.BlockName

namespace Unicode

/-- Get block name for a code point.

  Unicode property: `Block`
-/
public def lookupBlockName (c : UInt32) : BlockNameOrNoBlock :=
  if h : TableLookupTables.BlockName.BetweenOrEqStartEnd c then
    match TableLookupTables.BlockName.getInsideSparseRangeValueTable c h with
    | some b => .blockName b
    | none => .noBlock
  else
    .noBlock


