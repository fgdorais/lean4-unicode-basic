/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.IdStart

namespace Unicode

/-- Check if code point has ID_Start property using lookup table -/
public abbrev lookupIDStart (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.IdStart.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.IdStart.IsInsideSparseRangeTable c h
  else
    False
