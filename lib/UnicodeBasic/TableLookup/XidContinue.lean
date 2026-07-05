/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.XidContinue

namespace Unicode

/-- Check if code point has XID_Continue property using lookup table -/
public abbrev lookupXIDContinue (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.XidContinue.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.XidContinue.IsInsideSparseRangeTable c h
  else
    False
