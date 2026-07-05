/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Structure containing supported character properties from `DerivedCoreProperties.txt` -/
public structure DerivedCoreProperties where
  /-- property `Grapheme_Base` -/
  public graphemeBase : Array (UInt32 × Option UInt32) := #[]
  /-- property `Grapheme_Extend` -/
  public graphemeExtend : Array (UInt32 × Option UInt32) := #[]
  /-- property `Indic_Conjunct_Break=Consonant` -/
  public indicConjunctBreakConsonant : Array (UInt32 × Option UInt32) := #[]
  /-- property `Indic_Conjunct_Break=Extend` -/
  public indicConjunctBreakExtend : Array (UInt32 × Option UInt32) := #[]
  /-- property `Indic_Conjunct_Break=Linker` -/
  public indicConjunctBreakLinker : Array (UInt32 × Option UInt32) := #[]

  /-- property `ID_Start` -/
  public idStart : Array (UInt32 × Option UInt32) := #[]
  /-- property `ID_Continue` -/
  public idContinue : Array (UInt32 × Option UInt32) := #[]
  /-- property `XID_Start` -/
  public xidStart : Array (UInt32 × Option UInt32) := #[]
  /-- property `XID_Continue` -/
  public xidContinue : Array (UInt32 × Option UInt32) := #[]
deriving Inhabited, Repr

/-- Raw string form `DerivedCoreProperties.txt` -/
protected def DerivedCoreProperties.txt := include_str "../../data-ucd/core/DerivedCoreProperties.txt"

public unsafe initialize DerivedCoreProperties.data : DerivedCoreProperties ←
  let stream := UCDStream.ofString DerivedCoreProperties.txt
  let mut list : DerivedCoreProperties := {}
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in DerivedCoreProperties.txt"
    if record[1]! == "ID_Start" then
      list := {list with idStart := list.idStart.push val}
    if record[1]! == "ID_Continue" then
      list := {list with idContinue := list.idContinue.push val}
    if record[1]! == "XID_Start" then
      list := {list with xidStart := list.xidStart.push val}
    if record[1]! == "XID_Continue" then
      list := {list with xidContinue := list.xidContinue.push val}
    if record[1]! == "Grapheme_Base" then
      list := {list with graphemeBase := list.graphemeBase.push val}
    if record[1]! == "Grapheme_Extend" then
      list := {list with graphemeExtend := list.graphemeExtend.push val}
    if record[1]! == "InCB" && record[2]! == "Consonant" then
      list := {list with indicConjunctBreakConsonant := list.indicConjunctBreakConsonant.push val}
    if record[1]! == "InCB" && record[2]! == "Extend" then
      list := {list with indicConjunctBreakExtend := list.indicConjunctBreakExtend.push val}
    if record[1]! == "InCB" && record[2]! == "Linker" then
      list := {list with indicConjunctBreakLinker := list.indicConjunctBreakLinker.push val}
  return list

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

/-- Check if code point has `ID_Start` property -/
@[inline]
public def DerivedCoreProperties.isIDStart (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.idStart
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `ID_Continue` property -/
@[inline]
public def DerivedCoreProperties.isIDContinue (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.idContinue
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `XID_Start` property -/
@[inline]
public def DerivedCoreProperties.isXIDStart (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.xidStart
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `XID_Continue` property -/
@[inline]
public def DerivedCoreProperties.isXIDContinue (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.xidContinue
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Grapheme_Base` property -/
@[inline]
public def DerivedCoreProperties.isGraphemeBase (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.graphemeBase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Grapheme_Extend` property -/
@[inline]
public def DerivedCoreProperties.isGraphemeExtend (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.graphemeExtend
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Indic_Conjunct_Break=Consonant` -/
@[inline]
public def DerivedCoreProperties.isIndicConjunctBreakConsonant (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.indicConjunctBreakConsonant
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Indic_Conjunct_Break=Extend` -/
@[inline]
public def DerivedCoreProperties.isIndicConjunctBreakExtend (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.indicConjunctBreakExtend
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Indic_Conjunct_Break=Linker` -/
@[inline]
public def DerivedCoreProperties.isIndicConjunctBreakLinker (code : UInt32) : Bool :=
  let data := DerivedCoreProperties.data.indicConjunctBreakLinker
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

end Unicode
