/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.GraphemeBase

namespace Unicode

/-- Check if code point has Grapheme_Base property using lookup table -/
public abbrev lookupGraphemeBase (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.GraphemeBase.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.GraphemeBase.IsInsideSparseRangeTable c h
  else
    False
