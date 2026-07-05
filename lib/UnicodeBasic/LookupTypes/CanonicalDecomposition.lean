/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Unicode

abbrev IsValidCanonicalDecompositionMapping (l : List UInt32) : Prop :=
  l.length = 1 ∨ l.length = 2 ∨ l.length = 3 ∨ l.length = 4

-- TODO: rename to CanonicalDecompositionMappingResult?

structure CanonicalDecomposition where
  mapping : List UInt32
  validMapping : IsValidCanonicalDecompositionMapping mapping := by decide
deriving Repr, DecidableEq, Hashable, Ord, BEq, ReflBEq, LawfulBEq

end Unicode
