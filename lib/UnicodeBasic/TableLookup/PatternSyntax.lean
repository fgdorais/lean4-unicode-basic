/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.PatternSyntax

namespace Unicode

/-- Check if code point has Pattern_Syntax property using lookup table -/
public abbrev lookupPatternSyntax (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.PatternSyntax.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.PatternSyntax.IsInsideSparseRangeTable c h
  else
    False
