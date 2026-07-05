/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Extender

namespace Unicode

/-- Check if code point has Extender property using lookup table -/
public abbrev lookupExtender (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.Extender.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.Extender.IsInsideSparseRangeTable c h
  else
    False
