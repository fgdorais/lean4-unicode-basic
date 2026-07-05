/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Script
public import UnicodeBasic.LookupTypes.ScriptExtensions
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.ScriptExtensions

namespace Unicode

/-- Get script extensions of a code point using lookup table

  Unicode property: `Script_Extensions` -/
public def lookupScriptExtensions (c : UInt32) : Array Script :=
  if h : TableLookupTables.ScriptExtensions.BetweenOrEqStartEnd c then
    match TableLookupTables.ScriptExtensions.lookupSparseKVTable? c h with
    | some entry => entry.scripts
    | none => #[]
  else
    #[]
