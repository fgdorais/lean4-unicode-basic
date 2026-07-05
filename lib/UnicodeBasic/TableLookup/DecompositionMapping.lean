/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasicCommon.Hangul
public import UnicodeBasicCommon.Types.DecompositionMapping
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.DecompositionMapping

namespace Unicode

/-- Get decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type` -/
public def lookupDecompositionMapping? (c : UInt32) : Option DecompositionMapping :=
  -- Hangul syllables
  if h : Hangul.Syllable.IsBtwBaseAndLast c then
    let s := Hangul.getSyllable c h
    match s.getTChar? with
    | some t => some { tag := none, mapping := [s.getLVChar, t], validMapping := Or.inr (Or.inl rfl) }
    | none => some { tag := none, mapping := [s.getLChar, s.getVChar], validMapping := Or.inr (Or.inl rfl) }
  else
    if h : TableLookupTables.DecompositionMapping.BetweenOrEqStartEnd c then
      TableLookupTables.DecompositionMapping.lookupSparseKVTable? c h
    else
      none
