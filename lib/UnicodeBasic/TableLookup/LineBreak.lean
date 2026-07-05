/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.LineBreak
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.LineBreak

namespace Unicode

/-- Get line break property using lookup table -/
public def lookupLineBreak (c : UInt32) : LineBreak :=
  if h : TableLookupTables.LineBreak.BetweenOrEqStartEnd c then
    (TableLookupTables.LineBreak.getInsideSparseRangeValueTable c h).getD .unknown -- Why not split LineBreak on without and with unknown? bc Chunk4 and Chunk7 return unknown
  else
    .unknown
