/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.IdContinue

namespace Unicode

/-- Check if code point has ID_Continue property using lookup table -/
public abbrev lookupIDContinue (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.IdContinue.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.IdContinue.IsInsideSparseRangeTable c h
  else
    False
