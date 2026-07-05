/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.GeneralCategory

namespace Unicode

/-- Binary search -/
@[specialize]
public partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

public def decodeGeneralCategory (c raw : UInt32) : GC :=
  let gcMask : UInt32 := GC.univ
  let gc : GC := raw &&& gcMask
  let parityBit := (raw >>> 31) &&& 1
  if gc == GC.LC then
    if (c &&& 1) == parityBit then GC.Lu else GC.Ll
  else if gc == GC.PG then
    if (c &&& 1) == parityBit then GC.Ps else GC.Pe
  else if gc == GC.PQ then
    if (c &&& 1) == parityBit then GC.Pi else GC.Pf
  else
    gc

public def lookupPropRange (c : UInt32) (table : Array (UInt32 × UInt32)) : Bool :=
  if table.size == 0 || c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
