/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.SimpleCaseFolding

namespace Unicode

/-- Get simple case folding of a code point using lookup table -/
public def lookupSimpleCaseFolding (c : UInt32) : UInt32 :=
  if h : TableLookupTables.SimpleCaseFolding.BetweenOrEqStartEnd c then
    (TableLookupTables.SimpleCaseFolding.lookupSparsePairTable? c h).getD c
  else
    c
