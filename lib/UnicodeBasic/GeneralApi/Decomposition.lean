/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.CanonicalCombiningClass
public import UnicodeBasic.TableLookup.CanonicalDecompositionMapping
public import UnicodeBasic.TableLookup.DecompositionMapping

/-!
  This file uses lookup tables:
  `CanonicalCombiningClass`, `CanonicalDecompositionMapping`,
  `DecompositionMapping`.
-/

namespace Unicode

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical combining class of character

  Unicode property: `Canonical_Combining_Class`
-/
public def getCanonicalCombiningClass (char : Char) : Nat :=
  -- ASCII shortcut
  if char.val < 0x80 then
    0
  else
    lookupCanonicalCombiningClass char.val

/-- Get canonical decomposition of character (`NFD`)

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
public def getCanonicalDecomposition (char : Char) : String :=
  -- ASCII shortcut
  if char.val < 0x80 then char.toString else
    String.ofList <| (lookupCanonicalDecompositionMapping char.val).map fun c => Char.ofNat c.toNat

/-- Get decomposition mapping of a character

  This is used in normalization to canonical decomposition (`NFD`) and compatibility
  decomposition (`NFKD`).

  Unicode properties:
  `Decomposition_Type`
  `Decomposition_Mapping` -/
public def getDecompositionMapping? (char : Char) : Option DecompositionMapping :=
  -- ASCII shortcut
  if char.val < 0x80 then
    none
  else
    lookupDecompositionMapping? char.val

end Unicode
