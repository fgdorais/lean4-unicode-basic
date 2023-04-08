/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.Types
import UnicodeBasic.UnicodeData

/-- Make a string from a character stream -/
@[inline]
partial def String.ofStream {σ} [Stream σ Char] (s : σ) : String :=
  let rec loop (s : σ) (str : String) : String :=
    match Stream.next? s with
    | some (c, s) => loop s (str.push c)
    | none => str
  loop s ""

namespace Unicode

/-!
  ## Canonical Ordering ##
-/

/-- Canonical ordering stream type

  Unicode property: `Canonical_Combining_Class`
-/
structure CanonicalOrdering (σ) [Stream σ Char] where
  /-- Input stream -/
  stream : σ
  /-- Processing queue -/
  queue : List (Char × Nat) := []
  /-- Output character queue -/
  chars : List Char := []

@[inline]
private partial def CanonicalOrdering.next? {σ} [Stream σ Char] : CanonicalOrdering σ → Option (Char × CanonicalOrdering σ)
| str@⟨_, _, c :: cs⟩ => some (c, {str with chars := cs})
| ⟨s, q, []⟩ =>
  match Stream.next? s with
  | some (c, s) =>
    let n : Nat := (getUnicodeData c).canonicalCombiningClass
    if n > 0 then
      next? {stream := s, queue := push c n q, chars := []}
    else
      next? {stream := s, queue := [(c,0)], chars := flush q []}
  | none => next? {stream := s, queue := [], chars := flush q []}
where
  /-- Add character to processing queue -/
  push (c₀ : Char) (n₀ : Nat) : List (Char × Nat) → List (Char × Nat)
  | [] => [(c₀,n₀)]
  | (c, n) :: q =>
    if n₀ < n then
      (c, n) :: push c₀ n₀ q
    else
      (c₀, n₀) :: (c, n) :: q
  /-- Flush the processing queue to the output queue -/
  flush : List (Char × Nat) → List Char → List Char
  | [], cs => cs
  | (c, _) :: q, cs => flush q (c :: cs)

instance (σ) [Stream σ Char] : Stream (CanonicalOrdering σ) Char where
  next? := CanonicalOrdering.next?

/-- Canonically reorder a string

  Unicode property: `Canonical_Combining_Class`
-/
@[inline]
def getCanonicalReordering (str : String) : String :=
  String.ofStream (σ := CanonicalOrdering Substring) {stream := str.toSubstring}

/-!
  ## Canonical & Compatibility Decomposition ##
-/

/-- General decomposition stream type

  `filter` selects which decompositions are applied. Canonical decompositions
  are always applied but only compatibility decompositions that pass the
  filter are applied.

  Unicode property: `Decomposition_Type`, `Decomposition_Mapping`
-/
structure Decomposition (σ) [Stream σ Char] (filter : CompatibilityTag → Bool) where
  stream : σ
  queue : List Char := []

@[inline]
private partial def Decomposition.next? {σ f} [Stream σ Char] : Decomposition σ f → Option (Char × Decomposition σ f)
| ⟨s, []⟩ =>
  match Stream.next? s with
  | some (c, s) => next? {stream := s, queue := [c]}
  | none => none
| ⟨s, c :: q⟩ =>
  match getUnicodeData c |>.decompositionMapping with
  | some ⟨none, cs⟩ =>
    next? {stream := s, queue := cs ++ q}
  | some ⟨some cat, cs⟩  =>
    if f cat then
      next? {stream := s, queue := cs ++ q}
    else
      some (c, {stream := s, queue := q})
  | none =>
    some (c, {stream := s, queue := q})

instance (σ f) [Stream σ Char] : Stream (Decomposition σ f) Char where
  next? := Decomposition.next?

/-- Canonical decomposition stream type

  Includes canonical reordering postprocessing step.

  Unicode property: `Decomposition_Type`, `Decomposition_Mapping`
-/
abbrev CanonicalDecomposition (σ) [Stream σ Char] :=
  CanonicalOrdering (Decomposition σ fun _ => false)

/-- Make canonical decomposition stream

  Unicode property: `Decomposition_Type`, `Decomposition_Mapping`
-/
protected abbrev CanonicalDecomposition.mk {σ} [Stream σ Char] (s : σ) :
  CanonicalDecomposition σ := {stream := {stream := s}}

/-- Compatibility decomposition stream type

  Includes canonical reordering postprocessing step.

  Unicode property: `Decomposition_Type`, `Decomposition_Mapping`
-/
abbrev CompatibilityDecomposition (σ) [Stream σ Char] :=
  CanonicalOrdering (Decomposition σ fun _ => true)

/-- Make compatibility decomposition stream

  Unicode property: `Decomposition_Type`, `Decomposition_Mapping`
-/
protected abbrev CompatibilityDecomposition.mk {σ} [Stream σ Char] (s : σ) :
  CompatibilityDecomposition σ := {stream := {stream := s}}

end Unicode
