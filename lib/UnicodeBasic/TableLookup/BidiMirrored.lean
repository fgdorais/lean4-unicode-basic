/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.BidiMirrored

namespace Unicode

/-- Check if code point is bidi mirrored using lookup table

  Unicode property: `Bidi_Mirrored`
-/
public def lookupBidiMirrored (c : UInt32) : Bool :=
  if h : TableLookupTables.BidiMirrored.BetweenOrEqStartEnd c then
    TableLookupTables.BidiMirrored.IsInsideSparseRangeTable c h
  else
    false
