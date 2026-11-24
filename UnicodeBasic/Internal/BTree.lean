/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! # B-trees for kernel-reducible table lookups

A `BTree β` is a range table in a form the kernel can evaluate. It is a binary search over the
rows of the table: each internal node is one step of that search, and each leaf holds a block of
consecutive ranges, where the search continues. The bounds of the ranges in a leaf are packed into
one `Nat`; their values are in a block of type `β`, whose layout is up to each table.

This module is internal and may change at any time.
-/

namespace Unicode.Internal

/-- B-tree of code point ranges, with values in blocks of type `β` (internal use only) -/
public inductive BTree (β : Type) where
  /-- Ranges `lo` to `hi - 1` of a table, with their bounds packed in `keys` and their values in
  `block` (internal use only) -/
  | leaf (lo hi keys : Nat) (block : β)
  /-- Ranges that start below `key` are in `left`, the others are in `right` (internal use
  only) -/
  | node (key : Nat) (left right : BTree β)

namespace BTree

-- The bounds of range `i` of a leaf are bits `42 * (i - lo)` to `42 * (i - lo) + 41` of `keys`:
-- `cmin` in the low 21 bits and `cmax` in the high 21 bits.

/-- First code point of range `i` of a leaf (internal use only) -/
@[expose] public def cmin (lo keys i : Nat) : Nat := keys >>> (42 * (i - lo)) &&& 0x1FFFFF

/-- Last code point of range `i` of a leaf (internal use only) -/
@[expose] public def cmax (lo keys i : Nat) : Nat := keys >>> (42 * (i - lo) + 21) &&& 0x1FFFFF

/-- Last range from `i` to `j - 1` of a leaf that starts at or below `c`, if `i` starts at or
below `c` (internal use only) -/
@[expose] public def search (c lo keys : Nat) : (fuel i j : Nat) → Nat
  | 0, i, _ => i
  | fuel + 1, i, j =>
    let mid := (i + j) / 2
    if i == mid then i
    else if c < cmin lo keys mid then search c lo keys fuel i mid
    else search c lo keys fuel mid j

/-- Block and offset in the block of the range containing `c`, if any (internal use only) -/
@[expose] public def find? (c : Nat) : BTree β → Option (β × Nat)
  | node key left right => if c < key then find? c left else find? c right
  | leaf lo hi keys block =>
    let i := search c lo keys (hi - lo) lo hi
    if cmin lo keys i ≤ c && c ≤ cmax lo keys i then some (block, i - lo) else none

end BTree
