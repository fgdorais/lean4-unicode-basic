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
public def Syllable.size := sizeLVT

/-- Starting code point for Hangul syllables -/
public def Syllable.base : UInt32 := 0xAC00

/-- Stopping code point for Hangul syllables -/
public def Syllable.last : UInt32 := ⟨0xAC00 + Syllable.size - 1, by decide⟩

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
public def Syllable.toLV : Syllable → Fin sizeLV
  | ⟨⟨l, hl⟩, ⟨v, hv⟩, _⟩ =>
    have : l * sizeV + v < sizeLV := calc
      _ < l * sizeV + sizeV := by apply Nat.add_lt_add_left; exact hv
      _ = (l + 1) * sizeV := by rw [Nat.add_one_mul]
      _ ≤ sizeL * sizeV := by apply Nat.mul_le_mul_right; exact hl
    ⟨l * sizeV + v, this⟩

public def Syllable.index (s : Syllable) : Fin Syllable.size :=
  match s.toLV, s.toT with
  | ⟨lv, hlv⟩, ⟨t, ht⟩ =>
    have : lv * sizeT + t < sizeL * sizeV * sizeT := calc
      _ < lv * sizeT + sizeT := by apply Nat.add_lt_add_left; exact ht
      _ = (lv + 1) * sizeT := by rw [Nat.add_one_mul]
      _ ≤ sizeL * sizeV * sizeT := by apply Nat.mul_le_mul_right; exact hlv
    ⟨lv * sizeT + t, this⟩

/-- Get short name for Hangul syllable -/
@[inline]
public def Syllable.getShortName (s : Syllable) : String := shortNameL[s.toL] ++ shortNameV[s.toV] ++ shortNameT[s.toT]

/-- Get L part character for syllable -/
public def Syllable.getLChar (s : Syllable) : Char :=
  .ofNat (baseL.toNat + s.toL)

/-- Get V part character for syllable -/
public def Syllable.getVChar (s : Syllable) : Char :=
  .ofNat (baseV.toNat + s.toV)

/-- Get LV part character for syllable -/
public def Syllable.getLVChar (s : Syllable) : Char :=
  .ofNat (base.toNat + sizeT * s.toLV)

/-- Get T part character for syllable -/
public def Syllable.getTChar? (s : Syllable) : Option Char :=
  if s.toT.val == 0 then none else
    return .ofNat (baseT.toNat + s.toT)

/-- Get Hangul syllable from code point -/
public def getSyllable? (code : UInt32) : Option Syllable :=
  if code < 0xAC00 then none else
    let index := (code - 0xAC00).toNat
    if h : index ≥ Syllable.size then none else
      have islt : index < sizeLVT := Nat.lt_of_not_ge h
      let lpart := index / sizeVT
      have lislt : lpart < sizeL := Nat.div_lt_of_lt_mul islt
      let vtpart := index % sizeVT
      have vtislt : vtpart < sizeVT := Nat.mod_lt _ (by decide)
      let vpart := vtpart / sizeT
      have vislt : vpart < sizeV := Nat.div_lt_of_lt_mul vtislt
      let tpart := vtpart % sizeT
      have tislt : tpart < sizeT := Nat.mod_lt _ (by decide)
      some ⟨⟨lpart, lislt⟩, ⟨vpart, vislt⟩, ⟨tpart, tislt⟩⟩

@[inherit_doc getSyllable?]
public def getSyllable! (code : UInt32) : Syllable :=
  match getSyllable? code with
  | some s => s
  | none => panic! "not a Hangul syllable"
