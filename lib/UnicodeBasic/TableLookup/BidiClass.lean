/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.BidiClass
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.BidiClass

namespace Unicode

/-- Get bidirectional class using the generated lookup table.

  Unicode property: `Bidi_Class` -/
public def lookupBidiClass (c : UInt32) : BidiClass :=
  if h : TableLookupTables.BidiClass.BetweenOrEqStartEnd c then
    TableLookupTables.BidiClass.getInsideDenseRangeValueTable c h
  else
    .L -- The original implementation defaulted to .BN (Boundary Neutral) for values outside/between ranges. However, in Unicode, any code point not explicitly listed in Bidi_Class defaults to .L (Left-to-Right).

