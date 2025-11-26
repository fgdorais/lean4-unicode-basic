/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import UnicodeBasic.Types
import all UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Structure containing supported character properties from `PropList.txt` -/
public structure PropList where
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

/-- Raw string form `PropList.txt` -/
protected def PropList.txt := include_str "../data/PropList.txt"

public unsafe def PropList.init : IO PropList := do
  let stream := UCDStream.ofString PropList.txt
  let mut list : PropList := {}
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in PropList.txt"
    if record[1]! == "Noncharacter_Code_Point" then
      list := {list with noncharacterCodePoint := list.noncharacterCodePoint.push val}
    if record[1]! == "White_Space" then
      list := {list with whiteSpace := list.whiteSpace.push val}
    if record[1]! == "Other_Math" then
      list := {list with otherMath := list.otherMath.push val}
    if record[1]! == "Other_Alphabetic" then
      list := {list with otherAlphabetic := list.otherAlphabetic.push val}
    if record[1]! == "Other_Lowercase" then
      list := {list with otherLowercase := list.otherLowercase.push val}
    if record[1]! == "Other_Uppercase" then
      list := {list with otherUppercase := list.otherUppercase.push val}
  return list

/-- Parsed data from `PropList.txt` -/
@[init PropList.init]
public protected def PropList.data : PropList := {}

-- TODO: stop reinventing the wheel!
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

/-- Check if code point has `White_Space` property from `PropList.txt` -/
@[inline]
public def PropList.isWhiteSpace (code : UInt32) : Bool :=
  let data := PropList.data.whiteSpace
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Math` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherMath (code : UInt32) : Bool :=
  let data := PropList.data.otherMath
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Alphabetic` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherAlphabetic (code : UInt32) : Bool :=
  let data := PropList.data.otherAlphabetic
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Lowercase` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherLowercase (code : UInt32) : Bool :=
  let data := PropList.data.otherLowercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Uppercase` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherUppercase (code : UInt32) : Bool :=
  let data := PropList.data.otherUppercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top
