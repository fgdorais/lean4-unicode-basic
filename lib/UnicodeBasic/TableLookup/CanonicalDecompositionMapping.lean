/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Hangul
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.CanonicalDecompositionMapping

namespace Unicode

/-- Get canonical decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
public def lookupCanonicalDecompositionMapping (c : UInt32) : List UInt32 :=
  -- Hangul syllables
  match Unicode.Hangul.getSyllable? c with
  | some s =>
    match s.getTChar? with
    | some t => [s.getLChar.val, s.getVChar.val, t.val]
    | none => [s.getLChar.val, s.getVChar.val]
  | none =>
    if h : TableLookupTables.CanonicalDecompositionMapping.BetweenOrEqStartEnd c then
      match TableLookupTables.CanonicalDecompositionMapping.lookupSparseKVTable? c h with
      | some l => l.mapping
      | none => [c]
    else
      [c]
