/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types.SentenceBreak
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.SentenceBreak

namespace Unicode

/-- Get sentence break property using lookup table -/
public def lookupSentenceBreak (c : UInt32) : MaybeSentenceBreak :=
  if h : TableLookupTables.SentenceBreak.BetweenOrEqStartEnd c then
    (TableLookupTables.SentenceBreak.getInsideSparseRangeValueTable c h).elim .other .nonOther
  else
    .other
