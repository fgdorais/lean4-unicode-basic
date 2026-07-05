/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.GraphemeExtend

namespace Unicode

/-- Check if code point has Grapheme_Extend property using lookup table -/
public abbrev lookupGraphemeExtend (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.GraphemeExtend.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.GraphemeExtend.IsInsideSparseRangeTable c h
  else
    False
