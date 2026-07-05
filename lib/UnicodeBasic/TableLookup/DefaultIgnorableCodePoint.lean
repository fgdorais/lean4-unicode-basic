/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.DefaultIgnorableCodePoint

namespace Unicode

/-- Check if code point is ignorable using lookup table

  Unicode property: `Default_Ignorable_Code_Point` -/
public abbrev lookupDefaultIgnorableCodePoint (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.DefaultIgnorableCodePoint.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.DefaultIgnorableCodePoint.IsInsideSparseRangeTable c h
  else
    False
