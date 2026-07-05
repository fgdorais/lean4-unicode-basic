/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.LookupTypes.CaseFolding
public import UnicodeBasic.TableLookupTables.CaseFolding

namespace Unicode

/-- Get case folding of a code point using lookup table -/
public def lookupCaseFolding (c : UInt32) : Array UInt32 :=
  if h : TableLookupTables.CaseFolding.BetweenOrEqStartEnd c then
    match TableLookupTables.CaseFolding.lookupSparseKVTable? c h with
    | some f => f.mapping.toList.toArray.map Char.val
    | none => #[]
  else
    #[]
