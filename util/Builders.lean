/-
Copyright © 2024-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData
public import UnicodeBasic

/-! # Table builders

Functions that read the UCD through UnicodeData and build the compressed tables written by
`MakeTables` and `MakeCLib`.
-/

open Unicode

public section

def compressProp (arr : Array (UInt32 × UInt32)) (noOverlap : Bool := true) : Id <| Array (UInt32 × UInt32) :=
  if h : arr.size > 0 then do
    let mut res := #[]
    let mut top := arr[0]
    for a in arr[1:] do
      if noOverlap && a.1 ≤ top.2 then
        panic! "overlap!"
      else if a.1 ≤ top.2 + 1 then
        top := (top.1, max a.2 top.2)
      else
        res := res.push top
        top := a
    return res.push top
  else #[]

def compressData [BEq α] (arr : Array (UInt32 × UInt32 × α)) (noOverlap : Bool := true) : Id <| Array (UInt32 × UInt32 × α) :=
  if h : arr.size > 0 then do
    let mut res := #[]
    let mut top := arr[0]
    for a in arr[1:] do
      if noOverlap && a.1 ≤ top.2.1 then
        panic! "overlap!"
      else if a.2.2 == top.2.2 && a.1 ≤ top.2.1 + 1 then
        top := (top.1, max a.2.1 top.2.1, top.2.2)
      else
        res := res.push top
        top := a
    return res.push top
  else #[]

def mergeProp (d : Array (Array (UInt32 × UInt32))) (noOverlap : Bool := true) : Array (UInt32 × UInt32) :=
  let data := d.flatten.qsort fun a b => a.1 < b.1
  compressProp data noOverlap

def mergeData [BEq α] (d : Array (Array (UInt32 × UInt32 × α))) (noOverlap : Bool := true) : Array (UInt32 × UInt32 × α) :=
  let data := d.flatten.qsort fun a b => a.1 < b.1
  compressData data noOverlap

def statsData (array : Array (UInt32 × UInt32 × α)) : Id <| Nat × Nat := do
  let mut ct := 0
  for (c₀, c₁, _) in array do
    ct := ct + (c₁.toNat - c₀.toNat)
  return (array.size, ct)

def statsProp (array : Array (UInt32 × UInt32)) : Id <| Nat × Nat := do
  let mut ct := 0
  for (c₀, c₁) in array do
    ct := ct + (c₁.toNat - c₀.toNat)
  return (array.size, ct)

def mkBidiClass : IO <| Array (UInt32 × UInt32 × BidiClass) := do
  let mut t := #[]
  for d in UnicodeData.data.get do
    if d.name.takeEnd 7 == ", Last>" then
      match t.back? with
      | some (c₀, _, bc) =>
        t := t.pop.push (c₀, d.code, bc)
      | none => unreachable!
    else
      match t.back? with
      | some (c₀, c₁, bc) =>
        if d.code = c₁ + 1 && d.bidi == bc then
          t := t.pop.push (c₀, c₁+1, bc)
        else
          t := t.push (d.code, d.code, d.bidi)
      | none =>
        t := t.push (d.code, d.code, d.bidi)
  return t

def mkBidiMirrored : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for d in UnicodeData.data.get do
    if d.bidiMirrored then
      match t.back? with
      | some (c₀, c₁) =>
        if d.code == c₁ + 1 then
          t := t.pop.push (c₀, d.code)
        else
          t := t.push (d.code, d.code)
      | none =>
        t := t.push (d.code, d.code)
  return t

def mkCanonicalCombiningClass : IO <| Array (UInt32 × UInt32 × Nat) := do
  let mut t := #[]
  for d in UnicodeData.data.get do
    if d.cc > 0 then
      match t.back? with
      | some (c₀, c₁, cc) =>
        if t.size != 0 && d.code == c₁ + 1 && d.cc == cc then
          t := t.pop.push (c₀, c₁+1, cc)
        else
          t := t.push (d.code, d.code, d.cc)
      | none =>
        t := t.push (d.code, d.code, d.cc)
  return t

def mkCanonicalDecompositionMapping : IO <| Array (UInt32 × List Char) := do
  let mut t := #[]
  for data in UnicodeData.data.get do
    match data.decomp with
    | some ⟨none, l⟩ =>
      t := t.push (data.code, fullDecomposition l)
    | _ => continue
  return t
where
  /-- Each step replaces the first character by its decomposition, so there are fewer steps than
  code points unless the mappings have a cycle -/
  fullDecomposition (l : List Char) : List Char := loop 0x110000 l
  loop : Nat → List Char → List Char
  | _, [] => unreachable!
  | 0, _ => panic! "cyclic canonical decomposition"
  | fuel + 1, h :: t =>
    match (getUnicodeData h).decomp with
    | some ⟨none, l⟩ => loop fuel (l ++ t)
    | _ => h :: t

def mkCaseMapping : IO <| Array (UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := do
  let mut t := #[]
  for data in UnicodeData.data.get do
    match data with
    | ⟨_, _, _, _, _, _, _, _, none, none, none⟩ => continue
    | ⟨c, _, _, _, _, _, _, _, um, lm, tm⟩ =>
      let uc := match um with | some uc => uc.val | _ => c
      let lc := match lm with | some lc => lc.val | _ => c
      let tc := match tm with | some tc => tc.val | _ => uc
      match t.back? with
      | some (c₀,c₁,m) =>
        if (c == c₁ + 1) && (m == (uc, lc, tc)) then
          t := t.pop.push (c₀, c, m)
        else
          t := t.push (c, c, uc, lc, tc)
      | _ =>
          t := t.push (c, c, uc, lc, tc)
  return t

def mkDecompositionMapping : IO <| Array (UInt32 × String) := do
  let mut t := #[]
  for data in UnicodeData.data.get do
    match data.decomp with
    | some ⟨none, l⟩ =>
      t := t.push (data.code, ";" ++ ";".intercalate (l.map (toHexStringRaw <| Char.val .)))
    | some ⟨some k, l⟩ =>
      t := t.push (data.code, s!"{k};" ++ ";".intercalate (l.map (toHexStringRaw <| Char.val ·)))
    | _ => continue
  return t

def Unicode.GC.PB : GC := (0x80000000 : UInt32)
def Unicode.GC.LC0 : GC := .LC
def Unicode.GC.LC1 : GC := .LC ||| .PB
def Unicode.GC.PG0 : GC := .PG
def Unicode.GC.PG1 : GC := .PG ||| .PB
def Unicode.GC.PQ0 : GC := .PQ
def Unicode.GC.PQ1 : GC := .PQ ||| .PB

def mkGC : IO <| Array (UInt32 × UInt32 × UInt32) := do
  let mut t := #[(0,0,GC.Cc)]
  for i in [1:UnicodeData.data.get.size] do
    let data := UnicodeData.data.get[i]!
    let c := data.code
    let k := data.gc
    if data.name.takeEnd 8 == ", First>" then
      t := t.push (c, c, k)
    else if data.name.takeEnd 7 == ", Last>" then
      let (c₀, _, k₀) := t.back!
      t := t.pop.push (c₀, c, k₀)
    else
      let (c₀, c₁, k₀) := t.back!
      if c == c₁ + 1 then
        if k == k₀ then
          t := t.pop.push (c₀, c, k)
        else if k == .Lu then
          if c &&& 1 == 0 then
            if k₀ == .LC0 || (c₀ == c₁ && k₀ == .Ll) then
              t := t.pop.push (c₀, c, .LC0)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .LC1 || (c₀ == c₁ && k₀ == .Ll) then
              t := t.pop.push (c₀, c, .LC1)
            else
              t := t.push (c, c, k)
        else if k == .Ll then
          if c &&& 1 == 0 then
            if k₀ == .LC1 || (c₀ == c₁ && k₀ == .Lu) then
              t := t.pop.push (c₀, c, .LC1)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .LC0 || (c₀ == c₁ && k₀ == .Lu) then
              t := t.pop.push (c₀, c, .LC0)
            else
              t := t.push (c, c, k)
        else if k == .Ps then
          if c &&& 1 == 0 then
            if k₀ == .PG0 || (c₀ == c₁ && k₀ == .Pe) then
              t := t.pop.push (c₀, c, .PG0)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .PG1 || (c₀ == c₁ && k₀ == .Pe) then
              t := t.pop.push (c₀, c, .PG1)
            else
              t := t.push (c, c, k)
        else if k == .Pe then
          if c &&& 1 == 0 then
            if k₀ == .PG1 || (c₀ == c₁ && k₀ == .Ps) then
              t := t.pop.push (c₀, c, .PG1)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .PG0 || (c₀ == c₁ && k₀ == .Ps) then
              t := t.pop.push (c₀, c, .PG0)
            else
              t := t.push (c, c, k)
        else if k == .Pi then
          if c &&& 1 == 0 then
            if k₀ == .PQ0 || (c₀ == c₁ && k₀ == .Pf) then
              t := t.pop.push (c₀, c, .PQ0)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .PQ1 || (c₀ == c₁ && k₀ == .Pf) then
              t := t.pop.push (c₀, c, .PQ1)
            else
              t := t.push (c, c, k)
        else if k == .Pf then
          if c &&& 1 == 0 then
            if k₀ == .PQ1 || (c₀ == c₁ && k₀ == .Pi) then
              t := t.pop.push (c₀, c, .PQ1)
            else
              t := t.push (c, c, k)
          else
            if k₀ == .PQ0 || (c₀ == c₁ && k₀ == .Pi) then
              t := t.pop.push (c₀, c, .PQ0)
            else
              t := t.push (c, c, k)
        else
          t := t.push (c, c, k)
      else
        t := t.push (c, c, k)
  return t

def mkGeneralCategory : IO <| Array (UInt32 × UInt32 × GC) := do
  let mut t := #[(0,0,.Cc)]
  for i in [1:UnicodeData.data.get.size] do
    let data := UnicodeData.data.get[i]!
    let c := data.code
    let k := data.gc
    if data.name.takeEnd 8 == ", First>" then
      t := t.push (c, c, k)
    else if data.name.takeEnd 7 == ", Last>" then
      match t.back! with
      | (c₀, _, k) =>
        t := t.pop.push (c₀, c, k)
    else
      let k :=
        if k == .Lu && (c &&& 1) == 0 && UnicodeData.data.get[i+1]!.code == c+1 then
          if UnicodeData.data.get[i+1]!.gc == .Ll
          then .LC
          else k
        else if k == .Ll && (c &&& 1) != 0 && UnicodeData.data.get[i-1]!.code == c-1 then
          if UnicodeData.data.get[i-1]!.gc == .Lu
          then .LC
          else k
        else if k == .Ps && (c &&& 1) == 0 && UnicodeData.data.get[i+1]!.code == c+1 then
          if UnicodeData.data.get[i+1]!.gc == .Pe
          then .PG
          else k
        else if k == .Pe && (c &&& 1) != 0 && UnicodeData.data.get[i-1]!.code == c-1 then
          if UnicodeData.data.get[i-1]!.gc == .Ps
          then .PG
          else k
        else if k == .Pi && (c &&& 1) == 0 && UnicodeData.data.get[i+1]!.code == c+1 then
          if UnicodeData.data.get[i+1]!.gc == .Pf
          then .PQ
          else k
        else if k == .Pf && (c &&& 1) != 0 && UnicodeData.data.get[i-1]!.code == c-1 then
          if UnicodeData.data.get[i-1]!.gc == .Pi
          then .PQ
          else k
        else k
      match t.back! with
      | (c₀, c₁, k₁) =>
        if c == c₁ + 1 && k == k₁ then
          t := t.pop.push (c₀, c, k)
        else
          t := t.push (c, c, k)
  return t

def mkNoncharacterCodePoint : Array (UInt32 × UInt32) :=
  PropList.data.get.noncharacterCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkName : IO <| Array (UInt32 × UInt32 × String) := do
  let mut t := #[(0,0,"<control>")]
  for i in [1:UnicodeData.data.get.size] do
    let data := UnicodeData.data.get[i]!
    let c := data.code
    let n := data.name.copy
    if n.takeEnd 8 == ", First>" then
      if "<CJK Ideograph".isPrefixOf n then
        t := t.push (c, c, "<cjk unified ideograph>")
      else if "<Tangut Ideograph".isPrefixOf n then
        t := t.push (c, c, "<tangut ideograph>")
      else if n.takeEnd 17 == "Surrogate, First>" then
        match t.back! with
        | (c₀, c₁, n₀) =>
          if c == c₁ + 1 && n₀ == "<surrogate>" then
            t := t.pop.push (c₀, c, "<surrogate>")
          else
            t := t.push (c, c, "<surrogate>")
      else if n.takeEnd 19 == "Private Use, First>" then
        t := t.push (c, c, "<private use>")
      else
        t := t.push (c, c, ((n.dropEnd 8).copy ++ ">").toLower)
    else if n.takeEnd 7 == ", Last>" then
      match t.back! with
      | (c₀, _, n₀) =>
        t := t.pop.push (c₀, c, n₀)
    else if n == "<control>" then
      match t.back! with
      | (c₀, _, n₀) =>
        if n₀ == "<control>" then
          t := t.pop.push (c₀, c, n₀)
        else
          t := t.push (c, c, "<control>")
    else if "CJK COMPATIBILITY IDEOGRAPH-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<cjk compatibility ideograph>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<cjk compatibility ideograph>")
    else if "KHITAN SMALL SCRIPT CHARACTER-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<khitan small script character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<khitan small script character>")
    else if "EGYPTIAN HIEROGLYPH-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<egyptian hieroglyph>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<egyptian hieroglyph>")
    else if "NUSHU CHARACTER-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<nushu character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<nushu character>")
    else if "TANGUT COMPONENT-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<tangut component>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<tangut component>")
    else
      match t.back! with
      | (c₀, c₁, n₀) =>
        if c == c₁ + 1 && n == n₀ then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, n)
  return mergeData #[t, mkNoncharacterCodePoint.map fun (c₀, c₁) => (c₀, c₁, "<noncharacter>")]

def mkNumericValue : IO <| Array (UInt32 × UInt32 × NumericType) := do
  let mut t := #[]
  for d in UnicodeData.data.get do
    match d.numeric with
    | some (.decimal 0) =>
      t := t.push (d.code, d.code + 9, NumericType.decimal 0)
    | some (.digit v) =>
      match t.back! with
      | (c₀, c₁, n@(NumericType.digit x)) =>
        let last := x.val + c₁.toNat - c₀.toNat
        if d.code == c₁ + 1 && v.val == last + 1 then
          t := t.pop.push (c₀, d.code, n)
        else
          t := t.push (d.code, d.code, .digit v)
      | _ =>
        t := t.push (d.code, d.code, .digit v)
    | some n@(.numeric _ _) =>
      t := t.push (d.code, d.code, n)
    | _ => continue
  return t

def mkOtherAlphabetic : Array (UInt32 × UInt32) :=
  PropList.data.get.otherAlphabetic.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherLowercase : Array (UInt32 × UInt32) :=
  PropList.data.get.otherLowercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherMath : Array (UInt32 × UInt32) :=
  PropList.data.get.otherMath.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherUppercase : Array (UInt32 × UInt32) :=
  PropList.data.get.otherUppercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherDefaultIgnorableCodePoint : Array (UInt32 × UInt32) :=
  PropList.data.get.otherDefaultIgnorableCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkPrependedConcatenationMark : Array (UInt32 × UInt32) :=
  PropList.data.get.prependedConcatenationMark.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkVariationSelector : Array (UInt32 × UInt32) :=
  PropList.data.get.variationSelector.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOther : Array (UInt32 × UInt32 × UInt32) :=
  let ol := mkOtherLowercase |>.map fun (c₀, c₁) => (c₀, c₁, 1)
  let ou := mkOtherUppercase |>.map fun (c₀, c₁) => (c₀, c₁, 2)
  let oa := mkOtherAlphabetic |>.filterMap fun (c₀, c₁) =>
    if c₀ ∈ #[0x0345, 0x24B6, 0x24D0, 0x1F130, 0x1F150, 0x1F170]
    then none
    else some (c₀, c₁, 3)
  let om := mkOtherMath |>.map fun (c₀, c₁) => (c₀, c₁, 4)
  mergeData #[ol, ou, oa, om]

def mkAlphabetic : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for (c₀, c₁, gc) in ← mkGeneralCategory do
    if gc ⊆ .LC ||| .Ll ||| .Lu ||| .Lt ||| .Lm ||| .Lo ||| .Nl then
      match t.back? with
      | some (a₀, a₁) =>
        if c₀ == a₁ + 1 then
          t := t.pop.push (a₀, c₁)
        else
          t := t.push (c₀, c₁)
      | none =>
        t := t.push (c₀, c₁)
    else continue
  return mergeProp #[t, mkOtherAlphabetic]

def mkCased : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun d =>
    if d.2.2 ∈ [.LC, .Ll, .Lu, .Lt] then
      some (d.1, d.2.1)
    else
      none
  return mergeProp #[t, mkOtherLowercase, mkOtherUppercase]

def mkDefaultIgnorableCodePoint : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun d =>
    if d.2.2 = .Cf then some (d.1, d.2.1) else none
  let t ← t.flatMapM fun (c₀, c₁) => do
    let mut u := #[]
    for c in [c₀.toNat:c₁.toNat+1] do
      let c := c.toUInt32
      if 0xFFF9 ≤ c && c ≤ 0xFFFB then continue
      if 0x13430 ≤ c && c ≤ 0x1343F then continue
      if PropList.isPrependedConcatenationMark c then continue
      if PropList.isWhiteSpace c then continue
      match u.back? with
      | some (a, b) =>
        if c = b+1 then
          u := u.pop.push (a, c)
        else
          u := u.push (c, c)
      | none =>
        u := u.push (c, c)
    return u
  return mergeProp #[t, mkOtherDefaultIgnorableCodePoint, mkVariationSelector]

def mkMath : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun
    | (c₀, c₁, .Sm) => some (c₀, c₁)
    | _ => none
  return mergeProp #[t, mkOtherMath]

def mkLowercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for (c₀, c₁, gc) in ← mkGeneralCategory do
    if gc = .Ll then
      t := t.push (c₀, c₁)
    else if gc = .LC then
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 != 0 then t := t.push (c.toUInt32, c.toUInt32)
    else continue
  return mergeProp #[t, mkOtherLowercase]

def mkTitlecase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for (c₀, c₁, gc) in ← mkGeneralCategory do
    if gc = .Lt then
      t := t.push (c₀, c₁)
    else continue
  return t

def mkUppercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for (c₀, c₁, gc) in ← mkGeneralCategory do
    if gc = .Lu then
      t := t.push (c₀, c₁)
    else if gc = .LC then
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 == 0 then t := t.push (c.toUInt32, c.toUInt32)
    else continue
  return mergeProp #[t, mkOtherUppercase]

def mkWhiteSpace : Array (UInt32 × UInt32) :=
  PropList.data.get.whiteSpace.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkScriptName : Array (UInt32 × String) :=
  let t := PropertyAliases.getValues! "Script" |>.map fun name =>
    let s := Script.ofAbbrev! <| PropertyValueAliases.getShortName! "Script" name
    (s.code, name.toString)
  t.qsort fun (a, _) (b, _) => a < b

def mkScriptExtensions : Array (UInt32 × UInt32 × Array Script) := Id.run do
  let mut r := #[]
  for (c₀, c₁, v) in ScriptExtensions.data.get.byCode do
    let v := v.qsort fun a b => a.code < b.code
    match r.back? with
    | some (d₀, d₁, w) =>
      if d₁ + 1 == c₀ && v == w then
        r := r.pop.push (d₀, c₁, v)
      else
        r := r.push (c₀, c₁, v)
    | none => r := r.push (c₀, c₁, v)
  return r

end
