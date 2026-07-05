/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

namespace Unicode.Hangul

public def shortNameL : Array String :=
  #["G", "GG", "N", "D", "DD", "R", "M", "B", "BB", "S",
    "SS", "", "J", "JJ", "C", "K", "T", "P", "H"]

public def shortNameV : Array String :=
  #["A", "AE", "YA", "YAE", "EO", "E", "YEO", "YE", "O", "WA",
    "WAE", "OE", "YO", "U", "WEO", "WE", "WI", "YU", "EU", "YI",
    "I"]

public def shortNameT : Array String :=
  #["", "G", "GG", "GS", "N", "NJ", "NH", "D", "L", "LG",
    "LM", "LB", "LS", "LT", "LP", "LH", "M", "B", "BS", "S",
    "SS", "NG", "J", "C", "K", "T", "P", "H"]

public abbrev sizeL := shortNameL.size -- 19
public abbrev sizeV := shortNameV.size -- 21
public abbrev sizeT := shortNameT.size -- 28
public abbrev sizeLV := sizeL * sizeV -- 399
public abbrev sizeVT := sizeV * sizeT -- 588
public abbrev sizeLVT := sizeL * sizeV * sizeT -- 11172

public abbrev baseL : UInt32 := 0x1100
public abbrev baseV : UInt32 := 0x1161
public abbrev baseT : UInt32 := 0x11A7

/-- Number of Hangul syllables -/
public abbrev Syllable.size := sizeLVT

/-- Starting code point for Hangul syllables -/
public abbrev Syllable.base : UInt32 := 0xAC00

/-- Stopping code point for Hangul syllables -/
public abbrev Syllable.last : UInt32 := ⟨0xAC00 + Syllable.size - 1, by decide⟩

public abbrev Syllable.IsBtwBaseAndLast (c : UInt32) := base ≤ c ∧ c ≤ last

/-- Hangul syllable type -/
public structure Syllable where
  /-- L part of syllable -/
  public toL : Fin sizeL
  /-- V part of syllable -/
  public toV : Fin sizeV
  /-- T part of syllable (0 means none) -/
  public toT : Fin sizeT := ⟨0, by decide⟩
deriving DecidableEq, Repr

public instance : Inhabited Syllable where
  default := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- LV part of syllable -/
public abbrev Syllable.toLV : Syllable → Fin sizeLV
  | ⟨⟨l, hl⟩, ⟨v, hv⟩, _⟩ =>
    have : l * sizeV + v < sizeLV := calc
      _ < l * sizeV + sizeV := by apply Nat.add_lt_add_left; exact hv
      _ = (l + 1) * sizeV := by rw [Nat.add_one_mul]
      _ ≤ sizeL * sizeV := by apply Nat.mul_le_mul_right; exact hl
    ⟨l * sizeV + v, this⟩

public abbrev Syllable.index (s : Syllable) : Fin Syllable.size :=
  match s.toLV, s.toT with
  | ⟨lv, hlv⟩, ⟨t, ht⟩ =>
    have : lv * sizeT + t < sizeL * sizeV * sizeT := calc
      _ < lv * sizeT + sizeT := by apply Nat.add_lt_add_left; exact ht
      _ = (lv + 1) * sizeT := by rw [Nat.add_one_mul]
      _ ≤ sizeL * sizeV * sizeT := by apply Nat.mul_le_mul_right; exact hlv
    ⟨lv * sizeT + t, this⟩

/-- Get short name for Hangul syllable -/
public abbrev Syllable.getShortName (s : Syllable) : String := shortNameL[s.toL] ++ shortNameV[s.toV] ++ shortNameT[s.toT]

/-- Get L part character for syllable -/
public abbrev Syllable.getLChar (s : Syllable) : Char :=
  .ofNat (baseL.toNat + s.toL)

/-- Get V part character for syllable -/
public abbrev Syllable.getVChar (s : Syllable) : Char :=
  .ofNat (baseV.toNat + s.toV)

/-- Get LV part character for syllable -/
public abbrev Syllable.getLVChar (s : Syllable) : Char :=
  .ofNat (base.toNat + sizeT * s.toLV)

/-- Get T part character for syllable -/
public abbrev Syllable.getTChar? (s : Syllable) : Option Char :=
  if s.toT.val == 0 then none else
    return .ofNat (baseT.toNat + s.toT)

public abbrev getSyllable (code : UInt32) (h : Hangul.Syllable.IsBtwBaseAndLast code) : Syllable :=
  let index := (code - Syllable.base).toNat
  let lpart := index / sizeVT
  have lislt : lpart < sizeL := by
    dsimp only [lpart, index]
    have h_sub : (code - Syllable.base).toNat = code.toNat - Syllable.base.toNat := by
      rw [UInt32.toNat_sub]
      have h_lt := UInt32.toNat_lt code
      have h_base : Syllable.base.toNat = 44032 := rfl
      have h_le : Syllable.base.toNat ≤ code.toNat := h.1
      omega
    have h_last : Syllable.last.toNat = 55203 := rfl
    have h_base : Syllable.base.toNat = 44032 := rfl
    have h_le_last : code.toNat ≤ Syllable.last.toNat := h.2
    have h_sizeL : sizeL = 19 := rfl
    have h_sizeVT : sizeVT = 588 := rfl
    rw [h_sub, h_base, h_sizeVT, h_sizeL]
    omega
  let vtpart := index % sizeVT
  have vtislt : vtpart < sizeVT := Nat.mod_lt _ (by decide)
  let vpart := vtpart / sizeT
  have vislt : vpart < sizeV := by exact Nat.div_lt_of_lt_mul vtislt
  let tpart := vtpart % sizeT
  have tislt : tpart < sizeT := Nat.mod_lt _ (by decide)
  ⟨⟨lpart, lislt⟩, ⟨vpart, vislt⟩, ⟨tpart, tislt⟩⟩

/-- Get Hangul syllable from code point -/
public abbrev getSyllable? (code : UInt32) : Option Syllable :=
  if h : Syllable.IsBtwBaseAndLast code then
    some (getSyllable code h)
  else
    none

@[inherit_doc getSyllable?]
public abbrev getSyllable! (code : UInt32) : Syllable :=
  if h : Syllable.base ≤ code ∧ code ≤ Syllable.last then
    getSyllable code h
  else
    panic! "not a Hangul syllable"
