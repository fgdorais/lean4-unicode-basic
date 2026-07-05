/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.PatternWhiteSpace

namespace Unicode

/-- Check if code point has Pattern_White_Space property using lookup table -/
public abbrev lookupPatternWhiteSpace (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.PatternWhiteSpace.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.PatternWhiteSpace.IsInsideSparseRangeTable c h
  else
    False
