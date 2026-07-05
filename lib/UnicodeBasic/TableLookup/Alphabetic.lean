/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Alphabetic

namespace Unicode

/-- Check if code point is alphabetic using lookup table

  Unicode property: `Alphabetic` -/
public abbrev lookupAlphabetic (v : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.Alphabetic.BetweenOrEqStartEnd v then
    Unicode.TableLookupTables.Alphabetic.IsInsideSparseRangeTable v h
  else
    False
