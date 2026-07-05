/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Hyphen

namespace Unicode

/-- Check if code point has Hyphen property using lookup table -/
public abbrev lookupHyphen (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.Hyphen.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.Hyphen.IsInsideSparseRangeTable c h
  else
    False
