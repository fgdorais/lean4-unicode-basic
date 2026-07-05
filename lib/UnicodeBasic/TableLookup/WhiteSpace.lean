/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.WhiteSpace

namespace Unicode

/-- Check if code point is a white space character using lookup table

  Unicode property: `White_Space` -/
public abbrev lookupWhiteSpace (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.WhiteSpace.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.WhiteSpace.IsInsideSparseRangeTable c h
  else
    False
