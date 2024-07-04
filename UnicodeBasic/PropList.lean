/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

structure PropList where
  /-- property `Noncharacter_Code_Point` -/
  noncharacterCodePoint : Array (UInt32 × Option UInt32) := #[]
  /-- property `White_Space` -/
  whiteSpace : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Math` -/
  otherMath : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Alphabetic` -/
  otherAlphabetic : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Lowercase` -/
  otherLowercase : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Uppercase` -/
  otherUppercase : Array (UInt32 × Option UInt32) := #[]
deriving Inhabited, Repr

protected def PropList.txt := include_str "../data/PropList.txt"

private unsafe def PropList.init : IO PropList := do
  let stream := UCDStream.ofString PropList.txt
  let mut list : PropList := {}
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.splitOn ".." with
      | [c] => (ofHexString! c.toString, none)
      | [c₀,c₁] => (ofHexString! c₀.toString, some <| ofHexString! c₁.toString)
      | _ => panic! "invalid record in PropList.txt"
    match record[1]!.toString with -- TODO: don't use toString
    | "Noncharacter_Code_Point" => list := {list with noncharacterCodePoint := list.noncharacterCodePoint.push val}
    | "White_Space" => list := {list with whiteSpace := list.whiteSpace.push val}
    | "Other_Math" => list := {list with otherMath := list.otherMath.push val}
    | "Other_Alphabetic" => list := {list with otherAlphabetic := list.otherAlphabetic.push val}
    | "Other_Lowercase" => list := {list with otherLowercase := list.otherLowercase.push val}
    | "Other_Uppercase" => list := {list with otherUppercase := list.otherUppercase.push val}
    | _ => continue
  return list

@[init PropList.init]
protected def PropList.data : PropList := {}

/-- Binary search -/
private partial def find (code : UInt32) (data : Array (UInt32 × Option UInt32)) (lo hi : Nat) : Nat :=
  assert! (hi ≤ data.size)
  assert! (lo < hi)
  assert! (data[lo]!.fst ≤ code)
  let mid := (lo + hi) / 2 -- NB: mid < hi because lo < hi
  if lo = mid then
    mid
  else
    if code < data[mid]!.fst then
      find code data lo mid
    else
      find code data mid hi

/-- Check if code point has `White_Space` property -/
@[inline]
def PropList.isWhiteSpace (code : UInt32) : Bool :=
  let data := PropList.data.whiteSpace
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Math` property -/
@[inline]
def PropList.isOtherMath (code : UInt32) : Bool :=
  let data := PropList.data.otherMath
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Alphabetic` property -/
@[inline]
def PropList.isOtherAlphabetic (code : UInt32) : Bool :=
  let data := PropList.data.otherAlphabetic
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Lowercase` property -/
@[inline]
def PropList.isOtherLowercase (code : UInt32) : Bool :=
  let data := PropList.data.otherLowercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Uppercase` property -/
@[inline]
def PropList.isOtherUppercase (code : UInt32) : Bool :=
  let data := PropList.data.otherUppercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

end Unicode
