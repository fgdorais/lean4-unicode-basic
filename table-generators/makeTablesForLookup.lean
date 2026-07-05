/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import MakeTablesForLookup.Common
import UnicodeData
import UnicodeBasicCommon.CharacterDatabase
import UnicodeBasicCommon.Types.Script

open Unicode

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

inductive TableDensity where
  | dense
  | sparse
deriving Repr, BEq, Inhabited

inductive TableLayoutShape where
  | pair
  | key
  | range
deriving Repr, BEq, Inhabited

inductive WhyInvalid where
  | unsorted
  | overlap
  | duplicateKey
  | reversedRange
  | tooManyValueFields
deriving Repr, BEq, Inhabited

structure TableLayoutKind where
  density : TableDensity
  kind : TableLayoutShape
  isInvalid : Option WhyInvalid := none
deriving Repr, BEq, Inhabited

structure TableLayoutReport where
  kind : TableLayoutKind
  start : UInt32
  stop : UInt32
  rowCount : Nat := 0
  codePointCount : Nat := 0
  valueFieldCount : Nat := 0
deriving Repr, Inhabited

inductive TableSize where
  | rows (rowCount : Nat)
  | ranges (rowCount : Nat) (spanCount : Nat)
deriving Repr, Inhabited

inductive TableLayoutSource where
  | none
  | pair (pairs : Array (UInt32 × UInt32))
  | range (ranges : Array (UInt32 × UInt32)) (valueFieldCount : Nat)
  | key (keys : Array UInt32)
deriving Inhabited

structure GeneratedTable where
  name : String
  size : TableSize
  rawLayout : TableLayoutSource
  layout : TableLayoutSource
  sorted : Bool := false
  render : String
deriving Inhabited

private def TableDensity.label : TableDensity → String
  | .dense => "dense"
  | .sparse => "sparse"

private def TableLayoutShape.label : TableLayoutShape → String
  | .pair => "pair"
  | .key => "key"
  | .range => "range"

private def WhyInvalid.label : WhyInvalid → String
  | .unsorted => "unsorted"
  | .overlap => "overlap"
  | .duplicateKey => "duplicate key"
  | .reversedRange => "reversed range"
  | .tooManyValueFields => "too many value fields"

private def TableLayoutKind.label : TableLayoutKind → String
  | k =>
    let base :=
      match k.density, k.kind with
      | .dense, .pair => "dense pair"
      | .sparse, .pair => "sparse pair"
      | .dense, .key => "dense key"
      | .sparse, .key => "sparse key"
      | .dense, .range => "dense range"
      | .sparse, .range => "sparse range"
    match k.isInvalid with
    | none => base
    | some why => s!"invalid {base} ({why.label})"

private def ansi (code : String) (s : String) : String :=
  let esc := String.singleton (Char.ofNat 27)
  s!"{esc}[{code}m{s}{esc}[0m"

private def bold (s : String) : String := ansi "1" s
private def dim (s : String) : String := ansi "2" s
private def blue (s : String) : String := ansi "34" s
private def cyan (s : String) : String := ansi "36" s
private def green (s : String) : String := ansi "32" s
private def yellow (s : String) : String := ansi "33" s
private def magenta (s : String) : String := ansi "35" s
private def red (s : String) : String := ansi "31" s

private def TableLayoutKind.coloredLabel : TableLayoutKind → String
  | k =>
    match k.isInvalid with
    | some _ => red k.label
    | none =>
      match k.density with
      | .dense =>
        match k.kind with
        | .pair => green "dense pair"
        | .key => cyan "dense key"
        | .range => green "dense range"
      | .sparse =>
        match k.kind with
        | .pair => yellow "sparse pair"
        | .key => magenta "sparse key"
        | .range => yellow "sparse range"

private def TableLayoutKind.emoji : TableLayoutKind → String
  | k =>
    match k.isInvalid with
    | some _ => "🔴"
    | none =>
      match k.density with
      | .dense => "🟢"
      | .sparse => "🟡"

private def TableLayoutReport.describe (r : TableLayoutReport) : String :=
  s!"Layout: {r.kind.label} [{toHexStringRaw r.start}..{toHexStringRaw r.stop}]; rows={r.rowCount}; codePoints={r.codePointCount}; valueFields={r.valueFieldCount}"

private def TableSize.describe : TableSize → String
  | .rows rowCount => s!"Size: {rowCount}"
  | .ranges rowCount spanCount => s!"Size: {rowCount} + {spanCount}"

private def analyzeRangeTable (ranges : Array (UInt32 × UInt32)) (valueFieldCount : Nat) : TableLayoutReport :=
  match ranges[0]? with
  | none => panic! "range table cannot be empty"
  | some (start, firstStop) =>
    let codePointCount := Id.run do
      let mut total := 0
      for (c₀, c₁) in ranges do
        total := total + (c₁.toNat + 1 - c₀.toNat)
      return total
    let (density, invalid?) := Id.run do
      let mut prevEnd := firstStop
      if start > firstStop then
        return (.sparse, some WhyInvalid.reversedRange)
      for (c₀, c₁) in ranges[1:] do
        if c₀ > c₁ then
          return (.sparse, some WhyInvalid.reversedRange)
        if c₀ < prevEnd + 1 then
          if c₀ ≤ prevEnd then
            return (.sparse, some WhyInvalid.overlap)
          return (.sparse, some WhyInvalid.unsorted)
        if c₀ != prevEnd + 1 then
          return (.sparse, none)
        prevEnd := c₁
      return (.dense, none)
    {
      kind := { density, kind := .range, isInvalid := invalid? },
      start,
      stop := ranges[ranges.size - 1]!.2,
      rowCount := ranges.size,
      codePointCount,
      valueFieldCount
    }

private def analyzeKeyTable (keys : Array UInt32) : TableLayoutReport :=
  match keys[0]? with
  | none => panic! "key table cannot be empty"
  | some start =>
    let stop := keys[keys.size - 1]!
    let (density, invalid?) := Id.run do
      let mut prev := start
      for k in keys[1:] do
        if k < prev then
          return (.sparse, some WhyInvalid.unsorted)
        if k == prev then
          return (.sparse, some WhyInvalid.duplicateKey)
        if k != prev + 1 then
          return (.sparse, none)
        prev := k
      return (.dense, none)
    {
      kind := { density, kind := .key, isInvalid := invalid? },
      start,
      stop,
      rowCount := keys.size,
      codePointCount := keys.size,
      valueFieldCount := 0
    }

private def analyzePairTable (pairs : Array (UInt32 × UInt32)) : TableLayoutReport :=
  match pairs[0]? with
  | none => panic! "pair table cannot be empty"
  | some (start, _) =>
    let stop := pairs[pairs.size - 1]!.1
    let (density, invalid?) := Id.run do
      let mut prev := start
      for (k, _) in pairs[1:] do
        if k < prev then
          return (.sparse, some WhyInvalid.unsorted)
        if k == prev then
          return (.sparse, some WhyInvalid.duplicateKey)
        if k != prev + 1 then
          return (.sparse, none)
        prev := k
      return (.dense, none)
    {
      kind := { density, kind := .pair, isInvalid := invalid? },
      start,
      stop,
      rowCount := pairs.size,
      codePointCount := pairs.size,
      valueFieldCount := 0
    }

private def analyzeLayoutSource : TableLayoutSource → TableLayoutReport
  | .none => panic! "layout source cannot be empty"
  | .pair pairs => analyzePairTable pairs
  | .range ranges valueFieldCount => analyzeRangeTable ranges valueFieldCount
  | .key keys => analyzeKeyTable keys

private def isSortedPairTable (table : Array (UInt32 × UInt32)) : Bool :=
  Id.run do
    match table[0]? with
    | none => true
    | some (_, first) =>
      let mut prev := first
      for (c₀, _) in table[1:] do
        if c₀ < prev then
          return false
        prev := c₀
      return true

private def isSortedKeyTable (table : Array (UInt32 × α)) : Bool :=
  Id.run do
    match table[0]? with
    | none => true
    | some (first, _) =>
      let mut prev := first
      for (c, _) in table[1:] do
        if c ≤ prev then
          return false
        prev := c
      return true

private def isSortedRangeTable (table : Array (UInt32 × UInt32 × α)) : Bool :=
  Id.run do
    match table[0]? with
    | none => true
    | some (firstStart, firstEnd, _) =>
      let mut prevStart := firstStart
      let mut prevEnd := firstEnd
      for (c₀, c₁, _) in table[1:] do
        if c₀ < prevStart || (c₀ == prevStart && c₁ < prevEnd) then
          return false
        prevStart := c₀
        prevEnd := c₁
      return true

private def sortPairTable (table : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  table.qsort fun (a0, _) (b0, _) => a0 < b0

private def sortKeyTable (table : Array (UInt32 × α)) : Array (UInt32 × α) :=
  table.qsort fun (a0, _) (b0, _) => a0 < b0

private def sortRangeTable (table : Array (UInt32 × UInt32 × α)) : Array (UInt32 × UInt32 × α) :=
  table.qsort fun (a0, a1, _) (b0, b1, _) =>
    a0 < b0 || (a0 == b0 && a1 < b1)

def mkBidiClass : IO <| Array (UInt32 × UInt32 × BidiClass) := do
  let mut t := #[]
  let mut start : UInt32 := 0
  let mut last := lookupDerivedBidiClass 0
  for i in [1:Unicode.max.toNat + 1] do
    let c : UInt32 := UInt32.ofNat i
    let bc := lookupDerivedBidiClass c
    if bc == last then
      continue
    else
      t := t.push (start, c - 1, last)
      start := c
      last := bc
  return t.push (start, Unicode.max, last)

def mkBidiMirrored : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for d in UnicodeData.data do
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

def mkBidiMirroringGlyph : Array (UInt32 × UInt32) := Id.run do
  let mut t := #[]
  let txt : String := BidiMirroring.txt
  let stream := UCDStream.ofString txt
  for record in stream do
    t := t.push (ofHexString! record[0]!, ofHexString! record[1]!)
  return t

def mkBidiBrackets : Array (UInt32 × UInt32 × BidiBracketType) := Id.run do
  let mut t := #[]
  let txt : String := BidiBrackets.txt
  let stream := UCDStream.ofString txt
  for record in stream do
    t := t.push (
      ofHexString! record[0]!,
      ofHexString! record[1]!,
      BidiBracketType.ofAbbrev! record[2]!
    )
  return t

def mkBlockName : Array (UInt32 × UInt32 × String) := Id.run do
  let mut t := #[]
  let txt : String := Blocks.txt
  let stream := UCDStream.ofString txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in Blocks.txt"
    t := t.push (c₀, c₁, record[1]!.toString)
  return t

def mkEastAsianWidth : Array (UInt32 × UInt32 × EastAsianWidth) := Id.run do
  let mut t := #[]
  let txt : String := EastAsianWidth.txt -- from DerivedEastAsianWidth.lean
  let stream := UCDStream.ofString txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in DerivedEastAsianWidth.txt"
    t := t.push (c₀, c₁, EastAsianWidth.ofAbbrev! record[1]!)
  return t

def mkVerticalOrientation : Array (UInt32 × UInt32 × VerticalOrientation) := Id.run do
  let mut t := #[]
  let txt : String := VerticalOrientation.txt
  let stream := UCDStream.ofString txt
  for record in stream do
    let (c₀, c₁) : UInt32 × UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in VerticalOrientation.txt"
    t := t.push (c₀, c₁, VerticalOrientation.ofAbbrev! record[1]!)
  return t

def mkCanonicalCombiningClass : IO <| Array (UInt32 × UInt32 × Nat) := do
  let mut t := #[]
  for d in UnicodeData.data do
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

partial def mkCanonicalDecompositionMapping : IO <| Array (UInt32 × List Char) := do
  let mut t := #[]
  for data in UnicodeData.data do
    match data.decomp with
    | some { tag := none, mapping := l, .. } =>
      t := t.push (data.code, fullDecomposition l)
    | _ => continue
  return t
where
  fullDecomposition : List Char → List Char
  | [] => unreachable!
  | h :: t =>
    match (getUnicodeData h).decomp with
    | some { tag := none, mapping := l, .. } => fullDecomposition (l ++ t)
    | _ => h :: t

def mkCaseMapping : IO <| Array (UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := do
  let mut t := #[]
  for data in UnicodeData.data do
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
  for data in UnicodeData.data do
    match data.decomp with
    | some { tag := none, mapping := l, .. } =>
      t := t.push (data.code, ";" ++ ";".intercalate (l.map (toHexStringRaw <| Char.val .)))
    | some { tag := some k, mapping := l, .. } =>
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
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
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
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
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
        if k == .Lu && (c &&& 1) == 0 && UnicodeData.data[i+1]!.code == c+1 then
          if UnicodeData.data[i+1]!.gc == .Ll
          then .LC
          else k
        else if k == .Ll && (c &&& 1) != 0 && UnicodeData.data[i-1]!.code == c-1 then
          if UnicodeData.data[i-1]!.gc == .Lu
          then .LC
          else k
        else if k == .Ps && (c &&& 1) == 0 && UnicodeData.data[i+1]!.code == c+1 then
          if UnicodeData.data[i+1]!.gc == .Pe
          then .PG
          else k
        else if k == .Pe && (c &&& 1) != 0 && UnicodeData.data[i-1]!.code == c-1 then
          if UnicodeData.data[i-1]!.gc == .Ps
          then .PG
          else k
        else if k == .Pi && (c &&& 1) == 0 && UnicodeData.data[i+1]!.code == c+1 then
          if UnicodeData.data[i+1]!.gc == .Pf
          then .PQ
          else k
        else if k == .Pf && (c &&& 1) != 0 && UnicodeData.data[i-1]!.code == c-1 then
          if UnicodeData.data[i-1]!.gc == .Pi
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
  PropList.data.noncharacterCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkName : IO <| Array (UInt32 × UInt32 × String) := do
  let mut t := #[(0,0,"<Control>")]
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
    let c := data.code
    let n := data.name.copy
    if n.takeEnd 8 == ", First>" then
      if "<CJK Ideograph".isPrefixOf n then
        t := t.push (c, c, "<CJK Unified Ideograph>")
      else if "<Tangut Ideograph".isPrefixOf n then
        t := t.push (c, c, "<Tangut Ideograph>")
      else if n.takeEnd 17 == "Surrogate, First>" then
        match t.back! with
        | (c₀, c₁, n₀) =>
          if c == c₁ + 1 && n₀ == "<Surrogate>" then
            t := t.pop.push (c₀, c, "<Surrogate>")
          else
            t := t.push (c, c, "<Surrogate>")
      else if n.takeEnd 19 == "Private Use, First>" then
        t := t.push (c, c, "<Private Use>")
      else
        t := t.push (c, c, (n.dropEnd 8).copy ++ ">")
    else if n.takeEnd 7 == ", Last>" then
      match t.back! with
      | (c₀, _, n₀) =>
        t := t.pop.push (c₀, c, n₀)
    else if n == "<control>" then
      match t.back! with
      | (c₀, _, n₀) =>
        if n₀ == "<Control>" then
          t := t.pop.push (c₀, c, n₀)
        else
          t := t.push (c, c, "<Control>")
    else if "CJK COMPATIBILITY IDEOGRAPH-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<CJK Compatibility Ideograph>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<CJK Compatibility Ideograph>")
    else if "KHITAN SMALL SCRIPT CHARACTER-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Khitan Small Script Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Khitan Small Script Character>")
    else if "NUSHU CHARACTER-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Nushu Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Nushu Character>")
    else if "TANGUT COMPONENT-".isPrefixOf n then
      match t.back! with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Tangut Component>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Tangut Component>")
    else
      match t.back! with
      | (c₀, c₁, n₀) =>
        if c == c₁ + 1 && n == n₀ then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, n)
  return mergeData #[t, mkNoncharacterCodePoint.map fun (c₀, c₁) => (c₀, c₁, "<Reserved>")]

def mkNumericValue : IO <| Array (UInt32 × UInt32 × NumericType) := do
  let mut t := #[]
  for c in [0:Unicode.max.toNat + 1] do
    let c := UInt32.ofNat c
    match getUnicodeData? c with
    | none => continue
    | some d =>
      match d.numeric with
      | some n =>
        t := t.push (d.code, d.code, n)
      | none => continue
  return t

def mkOtherAlphabetic : Array (UInt32 × UInt32) :=
  PropList.data.otherAlphabetic.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherLowercase : Array (UInt32 × UInt32) :=
  PropList.data.otherLowercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherMath : Array (UInt32 × UInt32) :=
  PropList.data.otherMath.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherUppercase : Array (UInt32 × UInt32) :=
  PropList.data.otherUppercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherDefaultIgnorableCodePoint : Array (UInt32 × UInt32) :=
  PropList.data.otherDefaultIgnorableCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkPrependedConcatenationMark : Array (UInt32 × UInt32) :=
  PropList.data.prependedConcatenationMark.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkVariationSelector : Array (UInt32 × UInt32) :=
  PropList.data.variationSelector.map fun
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
  PropList.data.whiteSpace.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkIDStart : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.idStart).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkIDContinue : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.idContinue).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkXIDStart : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.xidStart).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkXIDContinue : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.xidContinue).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkDash : Array (UInt32 × UInt32) :=
  PropList.data.dash.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkHyphen : Array (UInt32 × UInt32) :=
  PropList.data.hyphen.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkQuotationMark : Array (UInt32 × UInt32) :=
  PropList.data.quotationMark.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkTerminalPunctuation : Array (UInt32 × UInt32) :=
  PropList.data.terminalPunctuation.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)


def mkExtender : Array (UInt32 × UInt32) :=
  PropList.data.extender.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkRegionalIndicator : Array (UInt32 × UInt32) :=
  PropList.data.regionalIndicator.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

private def hexStr (c : UInt32) : String := s!"0x{toHexStringRaw c}"

def mkCaseFolding : Array (UInt32 × String) :=
  (CaseFolding.data).filterMap fun e =>
    if e.status == 'C' || e.status == 'F' then
      let s := String.ofList (e.mapping.toList.map fun val => Char.ofNat val.toNat)
      some (e.code, s)
    else
      none

def mkSimpleCaseFolding : Array (UInt32 × UInt32) :=
  (CaseFolding.data).filterMap fun e =>
    if (e.status == 'C' || e.status == 'S') && e.mapping.size == 1 then
      some (e.code, e.mapping[0]!)
    else
      none

def mkGraphemeBreak : Array (UInt32 × UInt32 × String) :=
  (BreakProperties.data.graphemeBreak).map fun (c₀, c₁, v) =>
    (c₀, match c₁ with | some c => c | none => c₀, MakeTablesForLookup.graphemeBreak v)

def mkWordBreak : Array (UInt32 × UInt32 × String) :=
  (BreakProperties.data.wordBreak).map fun (c₀, c₁, v) =>
    (c₀, match c₁ with | some c => c | none => c₀, MakeTablesForLookup.wordBreak v)


def mkDiacritic : Array (UInt32 × UInt32) :=
  PropList.data.diacritic.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkSentenceTerminal : Array (UInt32 × UInt32) :=
  PropList.data.sentenceTerminal.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkPatternSyntax : Array (UInt32 × UInt32) :=
  PropList.data.patternSyntax.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkPatternWhiteSpace : Array (UInt32 × UInt32) :=
  PropList.data.patternWhiteSpace.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)


def mkEmoji : Array (UInt32 × UInt32) :=
  (EmojiData.data.emoji).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkEmojiPresentation : Array (UInt32 × UInt32) :=
  (EmojiData.data.emojiPresentation).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkEmojiModifier : Array (UInt32 × UInt32) :=
  (EmojiData.data.emojiModifier).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkEmojiModifierBase : Array (UInt32 × UInt32) :=
  (EmojiData.data.emojiModifierBase).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkEmojiComponent : Array (UInt32 × UInt32) :=
  (EmojiData.data.emojiComponent).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkExtendedPictographic : Array (UInt32 × UInt32) :=
  (EmojiData.data.extendedPictographic).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkSentenceBreak : Array (UInt32 × UInt32 × String) :=
  (BreakProperties.data.sentenceBreak).map fun (c₀, c₁, v) =>
    (c₀, match c₁ with | some c => c | none => c₀, MakeTablesForLookup.sentenceBreak v)

def mkLineBreak : Array (UInt32 × UInt32 × String) :=
  (BreakProperties.data.lineBreak).map fun (c₀, c₁, v) =>
    (c₀, match c₁ with | some c => c | none => c₀, MakeTablesForLookup.lineBreak v)

def mkGraphemeBase : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.graphemeBase).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkGraphemeExtend : Array (UInt32 × UInt32) :=
  (DerivedCoreProperties.data.graphemeExtend).map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkScript : Array (UInt32 × UInt32 × String) := Id.run do
  let t := Scripts.data.toArray.flatMap fun (sc, ranges) =>
    let sc := Script.ofAbbrev! <| (PropertyValueAliases.getShortName! "sc" sc).copy
    ranges.map fun (c₀, c₁) => (c₀, c₁, sc.toAbbrev)
  return t.qsort fun (a, _, _) (b, _, _) => a < b

private structure ScriptExtensionsValue where
  lastCode : UInt32
  scripts : Array Script

private def showScriptExtensionsValue (v : ScriptExtensionsValue) : String :=
  let scripts := v.scripts.map fun sc => s!"Script.mk {hexStr sc.code}"
  s!"ScriptExtensionsEntry.mk {hexStr v.lastCode} #[{", ".intercalate scripts.toList}]"

def mkScriptExtensions : Array (UInt32 × ScriptExtensionsValue) := Id.run do
  let mut t_arr : Array (UInt32 × ScriptExtensionsValue) := #[]
  let txt : String := ScriptExtensions.txt
  let stream := UCDStream.ofString txt
  for record in stream do
    let r0 : String.Slice := record[0]!
    let (c₀, c₁) : UInt32 × UInt32 :=
      match r0.split ".." |>.toList with
      | [c] => (ofHexString! c, ofHexString! c)
      | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
      | _ => panic! "invalid record in ScriptExtensions.txt"
    let r1 : String.Slice := record[1]!
    let scripts := r1.split " " |>.toArray |>.map Script.ofAbbrev!
    for c in [c₀.toNat:c₁.toNat + 1] do
      let c := UInt32.ofNat c
      t_arr := t_arr.push (c, { lastCode := c, scripts := scripts })
  return t_arr

private def showBidiClass : BidiClass → String
  | .leftToRight => "BidiClass.leftToRight"
  | .rightToLeft => "BidiClass.rightToLeft"
  | .arabicLetter => "BidiClass.arabicLetter"
  | .europeanNumber => "BidiClass.europeanNumber"
  | .europeanSeparator => "BidiClass.europeanSeparator"
  | .europeanTerminator => "BidiClass.europeanTerminator"
  | .arabicNumber => "BidiClass.arabicNumber"
  | .commonSeparator => "BidiClass.commonSeparator"
  | .nonspacingMark => "BidiClass.nonspacingMark"
  | .boundaryNeutral => "BidiClass.boundaryNeutral"
  | .paragraphSeparator => "BidiClass.paragraphSeparator"
  | .segmentSeparator => "BidiClass.segmentSeparator"
  | .whiteSpace => "BidiClass.whiteSpace"
  | .otherNeutral => "BidiClass.otherNeutral"
  | .leftToRightEmbedding => "BidiClass.leftToRightEmbedding"
  | .leftToRightOverride => "BidiClass.leftToRightOverride"
  | .rightToLeftEmbeding => "BidiClass.rightToLeftEmbeding"
  | .rightToLeftOverride => "BidiClass.rightToLeftOverride"
  | .popDirectionalFormat => "BidiClass.popDirectionalFormat"
  | .leftToRightIsolate => "BidiClass.leftToRightIsolate"
  | .rightToLeftIsolate => "BidiClass.rightToLeftIsolate"
  | .firstStrongIsolate => "BidiClass.firstStrongIsolate"
  | .popDirectionalIsolate => "BidiClass.popDirectionalIsolate"

private def showNumericType : NumericType → String
  | .decimal v => s!"NumericType.decimal ⟨{v.val}, by decide⟩"
  | .digit v => s!"NumericType.digit ⟨{v.val}, by decide⟩"
  | .numeric n none => s!"NumericType.numeric {n} none"
  | .numeric n (some d) => s!"NumericType.numeric ({n}) (some {d})"


private def lines (rows : Array String) : String :=
  String.intercalate "\n" rows.toList ++ "\n"

private def spaces (n : Nat) : String :=
  String.ofList <| List.replicate n ' '

private def isDenseRange (ranges : Array (UInt32 × UInt32)) : Bool :=
  if ranges.size ≤ 1 then true
  else
    Id.run do
      let mut prevEnd := ranges[0]!.2
      for (c₀, c₁) in ranges[1:] do
        if c₀ != prevEnd + 1 then return false
        prevEnd := c₁
      return true

private def isDenseKeyArray (keys : Array UInt32) : Bool :=
  if keys.size ≤ 1 then true
  else
    Id.run do
      let mut prev := keys[0]!
      for k in keys[1:] do
        if k != prev + 1 then return false
        prev := k
      return true

private def rangeBoundsText (start stop : UInt32) : String :=
  s!"abbrev start : UInt32 := {hexStr start}\n\nabbrev «end» : UInt32 := {hexStr stop}\n\nabbrev BetweenOrEqStartEnd (v : UInt32) : Prop := start ≤ v ∧ v ≤ «end»\n\n"

private def propTableText (table : Array (UInt32 × UInt32)) : String :=
  String.intercalate ",\n" <| table.toList.map fun (c₀, c₁) =>
    s!"  ({hexStr c₀}, {hexStr c₁})"

private def pairTableText (table : Array (UInt32 × UInt32)) : String :=
  String.intercalate ",\n" <| table.toList.map fun (c, v) =>
    s!"  ({hexStr c}, {hexStr v})"

private def keyTableText (showValue : α → String) (table : Array (UInt32 × α)) : String :=
  String.intercalate ",\n" <| table.toList.map fun (c, v) =>
    s!"  ({hexStr c}, {showValue v})"

private def rangeTableText (showValue : α → String) (table : Array (UInt32 × UInt32 × α)) : String :=
  String.intercalate ",\n" <| table.toList.map fun (c₀, c₁, v) =>
    s!"  ({hexStr c₀}, {hexStr c₁}, {showValue v})"

-- Compute the maximum depth of the balanced BST produced by the bst* functions.
-- The split is always at mid = n / 2; the pivot is taken from rest, so:
--   left  subtree has mid elements
--   right subtree has (n - mid - 1) elements
private partial def bstDepth (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else
    let mid := n / 2
    let leftSize  := mid
    let rightSize := n - mid - 1
    1 + max (bstDepth leftSize) (bstDepth rightSize)

-- Lean's elaborator struggles with deeply nested if-then-else Prop chains.
-- A depth beyond this threshold is likely to cause `isDefEq` heartbeat timeouts.
private def bstDepthWarnThreshold : Nat := 10

-- Balanced BST for prop membership over sorted non-overlapping ranges.
-- Returns Prop. O(log n) depth avoids Lean's maxRecDepth during elaboration.
private partial def bstPropChain (ranges : List (UInt32 × UInt32)) (ind : Nat) : String :=
  match ranges with
  | [] => "False"
  | [(c₀, c₁)] =>
    if c₀ == c₁ then s!"v = {hexStr c₀}"
    else s!"{hexStr c₀} ≤ v ∧ v ≤ {hexStr c₁}"
  | _ =>
    let mid := ranges.length / 2
    let (leftRanges, rest) := ranges.splitAt mid
    match rest with
    | [] => bstPropChain leftRanges ind
    | (c₀, c₁) :: rightRanges =>
      let sp := spaces ind
      let l := bstPropChain leftRanges (ind + 2)
      let r := bstPropChain rightRanges (ind + 2)
      s!"if v < {hexStr c₀} then\n{sp}  {l}\n{sp}else if {hexStr c₁} < v then\n{sp}  {r}\n{sp}else True"

def magicInstanceMaxSize : String -> Nat
| "Grapheme_Base" | "XID_Continue" | "ID_Continue" => 5096
| "Extender" | "Emoji" | "Other_Uppercase" | "White_Space" | "XID_Start"
| "Other_Lowercase" | "Math" | "ID_Start" | "Other_Alphabetic"
| "Terminal_Punctuation" | "Sentence_Terminal" | "Other_Math" | "Hyphen"
| "Grapheme_Extend" | "Pattern_Syntax" | "Pattern_White_Space"
| "Emoji_Presentation" | "Alphabetic" | "Quotation_Mark" | "Lowercase"
| "Emoji_Modifier_Base" | "Extended_Pictographic"
| "Diacritic" | "Uppercase" | "Emoji_Component" | "Dash"
| "Bidi_Mirrored" | "Default_Ignorable_Code_Point" | "Cased" => 4096
| moduleName => panic! s!"unknown module {moduleName} wants to generate Decidable (IsInsideSparseRangeTable...)"

-- The Decidable instance uses `unfold + infer_instance`. The BST can have ~2000 synthesis steps,
-- so we emit a file-level set_option (not `in`-scoped, to ensure the instance is registered globally).
private def sparseRangeMembershipText (moduleName : String) (ranges : Array (UInt32 × UInt32)) : String :=
  if ranges.isEmpty then ""
  else
    s!"@[inline_if_reduce, reducible]\ndef IsInsideSparseRangeTable (v : UInt32) (_h : BetweenOrEqStartEnd v) : Prop :=\n  {bstPropChain ranges.toList 2}\n\n" ++
    s!"set_option synthInstance.maxSize {magicInstanceMaxSize moduleName} in\ninstance (v : UInt32) (h : BetweenOrEqStartEnd v) : Decidable (IsInsideSparseRangeTable v h) := by\n  unfold IsInsideSparseRangeTable; infer_instance\n"

-- Balanced BST for sparse range value lookup (returns Option V).
private partial def bstSparseValueChain (showValue : α → String) (ranges : List (UInt32 × UInt32 × α)) (ind : Nat) : String :=
  match ranges with
  | [] => "none"
  | [(c₀, c₁, v)] =>
    if c₀ == c₁ then s!"if v == {hexStr c₀} then some ({showValue v}) else none"
    else s!"if {hexStr c₀} ≤ v ∧ v ≤ {hexStr c₁} then some ({showValue v}) else none"
  | _ =>
    let mid := ranges.length / 2
    let (leftRanges, rest) := ranges.splitAt mid
    match rest with
    | [] => bstSparseValueChain showValue leftRanges ind
    | (c₀, c₁, v) :: rightRanges =>
      let sp := spaces ind
      let l := bstSparseValueChain showValue leftRanges (ind + 2)
      let r := bstSparseValueChain showValue rightRanges (ind + 2)
      s!"if v < {hexStr c₀} then\n{sp}  {l}\n{sp}else if {hexStr c₁} < v then\n{sp}  {r}\n{sp}else some ({showValue v})"

private def sparseRangeLookupText (lookupName returnType : String) (showValue : α → String) (table : Array (UInt32 × UInt32 × α)) : String :=
  if table.isEmpty then ""
  else
    -- `Name` is rendered via chunk files below, so the heartbeat override is
    -- only kept for other generated lookup modules that still need it.
    s!"@[inline_if_reduce, reducible]\ndef {lookupName} (v : UInt32) (_h : BetweenOrEqStartEnd v) : Option {returnType} :=\n  {bstSparseValueChain showValue table.toList 2}\n"

private def chunkArray (size : Nat) (rows : Array α) : Array (Array α) := Id.run do
  let mut chunks := #[]
  let mut chunk := #[]
  for row in rows do
    chunk := chunk.push row
    if chunk.size == size then
      chunks := chunks.push chunk
      chunk := #[]
  if !chunk.isEmpty then
    chunks := chunks.push chunk
  return chunks

private def duplicateReturnedStrings (rows : Array (UInt32 × UInt32 × String)) : Array String := Id.run do
  let values := rows.map fun (_, _, s) => s
  let sorted := values.qsort fun a b => a < b
  let mut dups := #[]
  let mut i := 0
  while i < sorted.size do
    let s := sorted[i]!
    let mut j := i + 1
    while j < sorted.size && sorted[j]! == s do
      j := j + 1
    if j - i > 1 then
      dups := dups.push s
    i := j
  return dups

private def duplicateReturnedStringName (dups : Array String) (s : String) : Option String := Id.run do
  for i in [0:dups.size] do
    if dups[i]! == s then
      return some s!"dup{i}"
  return none

private def renderDuplicatedReturnedStringsModule (dups : Array String) : String :=
  let body := Id.run do
    let mut lines : Array String := #[]
    for i in [0:dups.size] do
      let s := dups[i]!
      lines := lines.push s!"-- {reprStr s}"
      lines := lines.push s!"abbrev dup{i} : String := {reprStr s}"
      if i + 1 < dups.size then
        lines := lines.push ""
    return lines
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "@[expose] public section", "", "namespace Unicode.TableLookupTables.Name.DuplicatedReturnedStrings", ""] ++
    body.toList ++
    ["", "end Unicode.TableLookupTables.Name.DuplicatedReturnedStrings", ""]

private def renderNameValue (dups : Array String) (s : String) : String :=
  match duplicateReturnedStringName dups s with
  | some dup => s!"Unicode.TableLookupTables.Name.DuplicatedReturnedStrings.{dup}"
  | none => reprStr s

private partial def bstSparseValueChainWith (showValue : α → String) (ranges : List (UInt32 × UInt32 × α)) (ind : Nat) : String :=
  bstSparseValueChain showValue ranges ind

-- Chunks should not be (of Name.lean will not build):
--
-- abbrev
-- @[inline] def
--
-- Chunks can be:
--
-- def
-- @[reducible] def
-- @[inline_if_reduce, reducible] def
private def renderNameChunkModule (idx : Nat) (chunk : Array (UInt32 × UInt32 × String)) (dups : Array String) : String :=
  let name := s!"Chunk{idx}"
  let showValue : String → String := renderNameValue dups
  let lookupBody := bstSparseValueChainWith showValue chunk.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasic.TableLookupTables.Name.DuplicatedReturnedStrings", "", "@[expose] public section", "", s!"namespace Unicode.TableLookupTables.Name.{name}", "", s!"@[inline_if_reduce, reducible]\ndef getInsideSparseRangeValueTable (v : UInt32) : Option String :=", s!"  {lookupBody}", "", s!"end Unicode.TableLookupTables.Name.{name}", ""]

private partial def nameChunkDispatchChain (chunks : List (UInt32 × String)) (ind : Nat) : String :=
  match chunks with
  | [] => "none"
  | [(_, call)] => call
  | (_, call₀) :: (nextStart, call₁) :: rest =>
      let sp := spaces ind
      let r := nameChunkDispatchChain ((nextStart, call₁) :: rest) (ind + 2)
      s!"if v < {hexStr nextStart} then\n{sp}  {call₀}\n{sp}else\n{sp}  {r}"

private def renderNameModule (chunks : Array (Array (UInt32 × UInt32 × String))) : String :=
  let calls := Id.run do
    let mut out : Array (UInt32 × String) := #[]
    for i in [0:chunks.size] do
      let chunk := chunks[i]!
      let start := chunk[0]!.1
      out := out.push (start, s!"Chunk{i}.getInsideSparseRangeValueTable v")
    return out
  let body := nameChunkDispatchChain calls.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasic.TableLookupTables.Name.DuplicatedReturnedStrings"] ++
    (List.range chunks.size |>.map fun i => s!"public import UnicodeBasic.TableLookupTables.Name.Chunk{i}") ++
    ["", "@[expose] public section", "", "namespace Unicode.TableLookupTables.Name", "", "abbrev start : UInt32 := 0x0000", "", "abbrev «end» : UInt32 := 0x10FFFF", "", "abbrev BetweenOrEqStartEnd (v : UInt32) : Prop := start ≤ v ∧ v ≤ «end»", "", "@[inline_if_reduce, reducible]", "def getInsideSparseRangeValueTable (v : UInt32) (_h : BetweenOrEqStartEnd v) : Option String :=", s!"  {body}", "", "end Unicode.TableLookupTables.Name", ""]

private def renderLineBreakChunkModule (idx : Nat) (chunk : Array (UInt32 × UInt32 × String)) : String :=
  let name := s!"Chunk{idx}"
  let lookupBody := bstSparseValueChain id chunk.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasicCommon.Types.LineBreak", "", "@[expose] public section", "", s!"namespace Unicode.TableLookupTables.LineBreak.{name}", "", s!"@[inline_if_reduce, reducible]\ndef getInsideSparseRangeValueTable (v : UInt32) : Option LineBreak :=", s!"  {lookupBody}", "", s!"end Unicode.TableLookupTables.LineBreak.{name}", ""]

private def toConstructorName (s : String) : String := Id.run do
  let mut words : List String := []
  let mut currWord := ""
  for c in s.toList do
    if c.isAlphanum then
      currWord := currWord.push c
    else
      if !currWord.isEmpty then
        words := words ++ [currWord]
        currWord := ""
  if !currWord.isEmpty then
    words := words ++ [currWord]
  match words with
  | [] => "empty"
  | head :: tail =>
    let headLower := head.toList.map (fun c => c.toLower) |> String.ofList
    let tailCamel := tail.map (fun w =>
      match w.toList with
      | [] => ""
      | h :: t => (h.toUpper :: t.map (fun c => c.toLower)) |> String.ofList
    )
    String.join (headLower :: tailCamel)

private def renderBlockNameTypes (table : Array (UInt32 × UInt32 × String)) : String :=
  let blockNames := table.map (fun (_, _, name) => name)
  let constructors := blockNames.map (fun name => s!"  | {toConstructorName name}")
  let toStringCases := table.map (fun (_, _, name) => s!"  | {toConstructorName name} => {reprStr name}")
  let ofStringCases := table.map (fun (_, _, name) => s!"  | {reprStr name} => some {toConstructorName name}")
  String.intercalate "\n" <| [
    "/- This file is generated by table-generators/makeTablesForLookup. -/",
    "module",
    "",
    "@[expose] public section",
    "",
    "namespace Unicode",
    "",
    "inductive BlockName where",
  ] ++ constructors.toList ++ [
    "  deriving DecidableEq, Inhabited, Repr",
    "",
    "namespace BlockName",
    "",
    "public def toString : BlockName → String",
  ] ++ toStringCases.toList ++ [
    "",
    "instance : ToString BlockName where",
    "  toString := toString",
    "",
    "public def ofString? : String → Option BlockName",
  ] ++ ofStringCases.toList ++ [
    "  | _ => none",
    "",
    "end BlockName",
    "",
    "inductive BlockNameOrNoBlock where",
    "  | blockName (block : BlockName)",
    "  | noBlock",
    "  deriving DecidableEq, Inhabited, Repr",
    "",
    "namespace BlockNameOrNoBlock",
    "",
    "public def toString : BlockNameOrNoBlock → String",
    "  | blockName b => b.toString",
    "  | noBlock => \"No_Block\"",
    "",
    "instance : ToString BlockNameOrNoBlock where",
    "  toString := toString",
    "",
    "public def ofString? : String → Option BlockNameOrNoBlock",
    "  | \"No_Block\" => some noBlock",
    "  | s => BlockName.ofString? s |>.map blockName",
    "",
    "end BlockNameOrNoBlock",
    "",
    "end Unicode",
    ""
  ]

private def renderLineBreakModule (chunks : Array (Array (UInt32 × UInt32 × String))) : String :=
  let calls := Id.run do
    let mut out : Array (UInt32 × String) := #[]
    for i in [0:chunks.size] do
      let chunk := chunks[i]!
      let start := chunk[0]!.1
      out := out.push (start, s!"Chunk{i}.getInsideSparseRangeValueTable v")
    return out
  let body := nameChunkDispatchChain calls.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasicCommon.Types.LineBreak"] ++
    (List.range chunks.size |>.map fun i => s!"public import UnicodeBasic.TableLookupTables.LineBreak.Chunk{i}") ++
    ["", "@[expose] public section", "", "namespace Unicode.TableLookupTables.LineBreak", "", "abbrev start : UInt32 := 0x0000", "", "abbrev «end» : UInt32 := 0x10FFFD", "", "abbrev BetweenOrEqStartEnd (v : UInt32) : Prop := start ≤ v ∧ v ≤ «end»", "", "@[inline_if_reduce, reducible]", "def getInsideSparseRangeValueTable (v : UInt32) (_h : BetweenOrEqStartEnd v) : Option LineBreak :=", s!"  {body}", "", "end Unicode.TableLookupTables.LineBreak", ""]

-- Balanced BST for dense range value lookup (returns V, total — no Option).
-- For dense tables every v in [start,end] belongs to exactly one range.
private partial def bstDenseValueChain (showValue : α → String) (ranges : List (UInt32 × UInt32 × α)) (ind : Nat) : String :=
  match ranges with
  | [] => panic! "empty dense chain"
  | [(_, _, v)] => showValue v
  | _ =>
    let mid := ranges.length / 2
    let (leftRanges, rest) := ranges.splitAt mid
    match rest with
    | [] => bstDenseValueChain showValue leftRanges ind
    | (c₀, c₁, v) :: rightRanges =>
      let sp := spaces ind
      let l := bstDenseValueChain showValue leftRanges (ind + 2)
      if rightRanges.isEmpty then
        s!"if v < {hexStr c₀} then\n{sp}  {l}\n{sp}else {showValue v}"
      else
        let r := bstDenseValueChain showValue rightRanges (ind + 2)
        s!"if v < {hexStr c₀} then\n{sp}  {l}\n{sp}else if {hexStr c₁} < v then\n{sp}  {r}\n{sp}else {showValue v}"

private def denseRangeLookupText (lookupName returnType : String) (showValue : α → String) (table : Array (UInt32 × UInt32 × α)) : String :=
  if table.isEmpty then ""
  else
    s!"@[inline_if_reduce, reducible]\ndef {lookupName} (v : UInt32) (_h : BetweenOrEqStartEnd v) : {returnType} :=\n  {bstDenseValueChain showValue table.toList 2}\n"

-- Balanced BST for exact key lookup (pair/KV tables, returns Option V).
private partial def bstExactLookupChain (showValue : α → String) (rows : List (UInt32 × α)) (ind : Nat) : String :=
  match rows with
  | [] => "none"
  | [(k, v)] => s!"if c == {hexStr k} then some ({showValue v}) else none"
  | _ =>
    let mid := rows.length / 2
    let (leftRows, rest) := rows.splitAt mid
    match rest with
    | [] => bstExactLookupChain showValue leftRows ind
    | (k, v) :: rightRows =>
      let sp := spaces ind
      let l := bstExactLookupChain showValue leftRows (ind + 2)
      let r := bstExactLookupChain showValue rightRows (ind + 2)
      s!"if c < {hexStr k} then\n{sp}  {l}\n{sp}else if c == {hexStr k} then some ({showValue v})\n{sp}else\n{sp}  {r}"

private def findDuplicateChars (rows : Array (UInt32 × String)) : Array Char := Id.run do
  let mut allChars : Array Char := #[]
  for (_, s) in rows do
    let parts := s.splitOn ";"
    for hex in parts.drop 1 do
      let c := Char.ofNat (ofHexString! hex.toSlice).toNat
      allChars := allChars.push c
  let sorted := allChars.qsort fun a b => a.toNat < b.toNat
  let mut dups := #[]
  let mut i := 0
  while i < sorted.size do
    let c := sorted[i]!
    let mut j := i + 1
    while j < sorted.size && sorted[j]! == c do
      j := j + 1
    if j - i > 1 then
      dups := dups.push c
    i := j
  return dups

private def findDuplicateChar (dups : Array Char) (c : Char) : Option String := Id.run do
  for i in [0:dups.size] do
    if dups[i]! == c then
      return some s!"dup{c.toNat}"
  return none

private def renderDuplicatedCharsModule (dups : Array Char) : String :=
  let body := Id.run do
    let mut lines : Array String := #[]
    for i in [0:dups.size] do
      let c := dups[i]!
      let val := if !(c.toNat < 32 || (c.toNat >= 127 && c.toNat < 160)) && c != ' ' && c != '\u00a0' then
        toString (repr c)
      else
        s!"Char.ofNat {c.toNat}"
      lines := lines.push s!"-- {c.toNat}"
      lines := lines.push s!"abbrev dup{c.toNat} : Char := {val}"
      if i + 1 < dups.size then
        lines := lines.push ""
    return lines
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "@[expose] public section", "", "namespace Unicode.TableLookupTables.DecompositionMapping.DuplicatedChars", ""] ++
    body.toList ++
    ["", "end Unicode.TableLookupTables.DecompositionMapping.DuplicatedChars", ""]

private def renderDecompositionMappingChunkModule (idx : Nat) (chunk : Array (UInt32 × String)) (showValue : String → String) : String :=
  let name := s!"Chunk{idx}"
  let lookupBody := bstExactLookupChain showValue chunk.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasic.TableLookupTables.DecompositionMapping.DuplicatedChars", "public import UnicodeBasicCommon.Types.DecompositionMapping", "", "open Unicode.TableLookupTables.DecompositionMapping.DuplicatedChars", "", "@[expose] public section", "", s!"namespace Unicode.TableLookupTables.DecompositionMapping.{name}", "", s!"@[inline_if_reduce, reducible]\ndef lookupSparseKVTable? (c : UInt32) : Option DecompositionMapping :=", s!"  {lookupBody}", "", s!"end Unicode.TableLookupTables.DecompositionMapping.{name}", ""]

private partial def decompChunkDispatchChain (chunks : List (UInt32 × String)) (ind : Nat) : String :=
  match chunks with
  | [] => "none"
  | [(_, call)] => call
  | (_, call₀) :: (nextStart, call₁) :: rest =>
      let sp := spaces ind
      let r := decompChunkDispatchChain ((nextStart, call₁) :: rest) (ind + 2)
      s!"if c < {hexStr nextStart} then\n{sp}  {call₀}\n{sp}else\n{sp}  {r}"

private def renderDecompositionMappingModule (chunks : Array (Array (UInt32 × String))) : String :=
  let calls := Id.run do
    let mut out : Array (UInt32 × String) := #[]
    for i in [0:chunks.size] do
      let chunk := chunks[i]!
      let start := chunk[0]!.1
      out := out.push (start, s!"Chunk{i}.lookupSparseKVTable? c")
    return out
  let body := decompChunkDispatchChain calls.toList 2
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module", "", "public import UnicodeBasic.TableLookupTables.DecompositionMapping.DuplicatedChars", "public import UnicodeBasicCommon.Types.DecompositionMapping"] ++
    (List.range chunks.size |>.map fun i => s!"public import UnicodeBasic.TableLookupTables.DecompositionMapping.Chunk{i}") ++
    ["", "@[expose] public section", "", "namespace Unicode.TableLookupTables.DecompositionMapping", "", "abbrev start : UInt32 := 0x00A0", "", "abbrev «end» : UInt32 := 0x2FA1D", "", "abbrev BetweenOrEqStartEnd (v : UInt32) : Prop := start ≤ v ∧ v ≤ «end»", "", "@[inline_if_reduce, reducible]", "def lookupSparseKVTable? (c : UInt32) (_h : BetweenOrEqStartEnd c) : Option DecompositionMapping :=", s!"  {body}", "", "end Unicode.TableLookupTables.DecompositionMapping", ""]


private def optionLookupText (lookupName returnType : String) (showValue : α → String) (table : Array (UInt32 × α)) : String :=
  if table.isEmpty then ""
  else
    let prefixOpt := if returnType == "DecompositionMapping" then "set_option maxHeartbeats 20000000 in\n" else ""
    prefixOpt ++ s!"@[inline_if_reduce, reducible]\ndef {lookupName} (c : UInt32) (_h : BetweenOrEqStartEnd c) : Option {returnType} :=\n  {bstExactLookupChain showValue table.toList 2}\n"

private def renderGeneratedTable (table : GeneratedTable) : String :=
  table.render

private def printIndented (indent : Nat) (s : String) : IO Unit :=
  IO.println <| spaces indent ++ s

private def logGeneratedTable (table : GeneratedTable) : IO Unit := do
  printIndented 0 s!"{bold "🧾"} {bold <| blue table.name}"
  printIndented 2 s!"{dim "size"} {bold ":"} {table.size.describe}"
  if table.sorted then
    let before := analyzeLayoutSource table.rawLayout
    let after := analyzeLayoutSource table.layout
    printIndented 2 s!"{dim "sort"} {bold ":"} yes"
    if before.kind != after.kind then
      printIndented 4 s!"{dim "structure"} {bold ":"} {before.kind.label} -> {after.kind.label}"
  let report := analyzeLayoutSource table.layout
  printIndented 2 s!"{dim "layout"} {bold ":"}"
  printIndented 4 s!"{report.kind.emoji} {report.kind.kind.label}"
  printIndented 6 s!"{dim "density"} {bold ":"} {report.kind.density.label}"
  printIndented 6 s!"{dim "value fields"} {bold ":"} {report.valueFieldCount}"
  match report.kind.isInvalid with
  | some why => printIndented 6 s!"{dim "invalid"} {bold ":"} {why.label}"
  | none => pure ()
  printIndented 6 s!"{dim "bounds"} {bold ":"} [{toHexStringRaw report.start}..{toHexStringRaw report.stop}]"
  printIndented 6 s!"{dim "rows"} {bold ":"} {report.rowCount}"
  printIndented 6 s!"{dim "code points"} {bold ":"} {report.codePointCount}"
  -- For sparse tables that use a BST lookup, print the tree depth.
  -- Dense tables use direct indexing and do not generate a BST.
  if report.kind.density == .sparse then
    let depth := bstDepth report.rowCount
    if depth > bstDepthWarnThreshold then
      printIndented 6 s!"{bold (red "⚠ bst depth")} {bold ":"} {bold (red (toString depth))} {red s!"(exceeds threshold {bstDepthWarnThreshold} — may cause elaboration heartbeat timeout)"}"
    else
      printIndented 6 s!"{dim "bst depth"} {bold ":"} {depth}"

private def mkPropTable (name : String) (table : Array (UInt32 × UInt32)) : GeneratedTable :=
  let (rowCount, spanCount) := statsProp table
  let sorted := sortPairTable table
  let head := sorted[0]!.1
  let tail := sorted[sorted.size - 1]!.2
  let isDense := isDenseRange sorted
  {
    name,
    size := .ranges rowCount spanCount,
    rawLayout := .range table 0,
    layout := .range sorted 0,
    sorted := !isSortedPairTable table,
    render :=
      rangeBoundsText head tail ++
      -- s!"public def table : Array (UInt32 × UInt32) := #[\n{propTableText sorted}\n]\n\n" ++
      if isDense then "" else sparseRangeMembershipText name sorted
  }

private def mkPairTable (name : String) (table : Array (UInt32 × UInt32)) : GeneratedTable :=
  let sorted := sortPairTable table
  let keys := sorted.map Prod.fst
  let head := keys[0]!
  let tail := keys[keys.size - 1]!
  let isDense := isDenseKeyArray keys
  let lookupName := if isDense then "lookupDensePairTable?" else "lookupSparsePairTable?"
  {
    name,
    size := .rows table.size,
    rawLayout := .pair table,
    layout := .pair sorted,
    sorted := !isSortedPairTable table,
    render :=
      rangeBoundsText head tail ++
      -- s!"public def table : Array (UInt32 × UInt32) := #[\n{pairTableText sorted}\n]\n\n" ++
      optionLookupText lookupName "UInt32" hexStr sorted
  }

private def mkRangeTable (name : String) (valueFieldCount : Nat) (valueType : String) (showValue : α → String) (table : Array (UInt32 × UInt32 × α)) : GeneratedTable :=
  let (rowCount, spanCount) := statsData table
  let sorted := sortRangeTable table
  match sorted[0]?, sorted.back? with
  | some (head, _, _), some (_, tail, _) =>
    let ranges := sorted.map fun (c₀, c₁, _) => (c₀, c₁)
    let isDense := isDenseRange ranges
    {
      name,
      size := .ranges rowCount spanCount,
      rawLayout := .range (table.map fun (c₀, c₁, _) => (c₀, c₁)) valueFieldCount,
      layout := .range ranges valueFieldCount,
      sorted := !isSortedRangeTable table,
      render :=
        rangeBoundsText head tail ++
        -- s!"public def table : Array (UInt32 × UInt32 × {valueType}) := #[\n{rangeTableText showValue sorted}\n]\n\n" ++
        if isDense then
          denseRangeLookupText "getInsideDenseRangeValueTable" valueType showValue sorted
        else
          sparseRangeLookupText "getInsideSparseRangeValueTable" valueType showValue sorted
    }
  | _, _ => panic! "range table cannot be empty"

private def mkKeyTable (name : String) (valueType : String) (showValue : α → String) (table : Array (UInt32 × α)) : GeneratedTable :=
  let sorted := sortKeyTable table
  let keys := sorted.map Prod.fst
  let isDense := isDenseKeyArray keys
  if isDense then panic! s!"dense key table not supported: {name}"
  else
    {
      name,
      size := .rows table.size,
      rawLayout := .key <| table.map Prod.fst,
      layout := .key <| sorted.map Prod.fst,
      sorted := !isSortedKeyTable table,
      render :=
        (match keys[0]?, keys.back? with
         | some head, some tail => rangeBoundsText head tail
         | _, _ => "") ++
        -- s!"public def table : Array (UInt32 × {valueType}) := #[\n{keyTableText showValue sorted}\n]\n\n" ++
        optionLookupText "lookupSparseKVTable?" valueType showValue sorted
    }

private def buildTable (name : String) : IO GeneratedTable := do
  match name with
  | "Alphabetic" =>
    let table ← mkAlphabetic
    return mkPropTable name table
  | "Bidi_Class" =>
    let table ← mkBidiClass
    return mkRangeTable name 1 "BidiClass" (fun v => s!"BidiClass.{v.toAbbrev}") table
  | "Bidi_Mirroring_Glyph" =>
    let table := mkBidiMirroringGlyph
    return mkPairTable name table
  | "Bidi_Brackets" =>
    let table := mkBidiBrackets
    let showBt : BidiBracketType → String := fun
      | .openBracket => "BidiBracketType.openBracket"
      | .closeBracket => "BidiBracketType.closeBracket"
    return mkKeyTable name "BidiBracket" (fun (paired, bt) => "BidiBracket.mk " ++ hexStr paired ++ " " ++ showBt bt) (table.map fun (c, p, bt) => (c, (p, bt)))
  | "Block_Name" =>
    let table := mkBlockName
    let converted := table.map fun (c₀, c₁, name) =>
      (c₀, c₁, s!"BlockName.{toConstructorName name}")
    return mkRangeTable name 1 "BlockName" id converted
  | "East_Asian_Width" =>
    let table := mkEastAsianWidth
    return mkRangeTable name 1 "EastAsianWidth" (fun w =>
      match w with
      | .ambiguous => "EastAsianWidth.ambiguous"
      | .fullwidth => "EastAsianWidth.fullwidth"
      | .halfwidth => "EastAsianWidth.halfwidth"
      | .neutral => "EastAsianWidth.neutral"
      | .narrow => "EastAsianWidth.narrow"
      | .wide => "EastAsianWidth.wide") table
  | "Vertical_Orientation" =>
    let table := mkVerticalOrientation
    return mkRangeTable name 1 "VerticalOrientation" (fun v =>
      match v with
      | .upright => "VerticalOrientation.upright"
      | .rotated => "VerticalOrientation.rotated"
      | .transformedUpright => "VerticalOrientation.transformedUpright"
      | .transformedRotated => "VerticalOrientation.transformedRotated") table
  | "Canonical_Combining_Class" =>
    let table ← mkCanonicalCombiningClass
    return mkRangeTable name 1 "Nat" toString table
  | "Canonical_Decomposition_Mapping" =>
    let table ← mkCanonicalDecompositionMapping
    return mkKeyTable name "CanonicalDecomposition" (fun l => s!"CanonicalDecomposition.mk [{", ".intercalate (l.map (fun c => hexStr c.val))}]") table
  | "Case_Mapping" =>
    let table ← mkCaseMapping
    return mkRangeTable name 3 "(UInt32 × UInt32 × UInt32)" (fun (uc, lc, tc) => s!"({hexStr uc}, {hexStr lc}, {hexStr tc})") table
  | "Cased" =>
    let table ← mkCased
    return mkPropTable name table
  | "Decomposition_Mapping" =>
    throw <| IO.userError "Decomposition_Mapping is generated using chunk module"
  | "Default_Ignorable_Code_Point" =>
    let table ← mkDefaultIgnorableCodePoint
    return mkPropTable name table
  | "General_Category" =>
    let table ← mkGC
    return mkRangeTable name 1 "UInt32" (fun c => s!"({c} : UInt32)") table
  | "Lowercase" =>
    let table ← mkLowercase
    return mkPropTable name table
  | "Math" =>
    let table ← mkMath
    return mkPropTable name table
  | "Name" =>
    let table ← mkName
    let sorted := sortRangeTable table
    if sorted.size > 0 then
      let ranges := sorted.map fun (c₀, c₁, _) => (c₀, c₁)
      let (rowCount, spanCount) := Id.run <| statsData sorted
      pure
        { name,
          size := .ranges rowCount spanCount,
          rawLayout := .range (table.map fun (c₀, c₁, _) => (c₀, c₁)) 1,
          layout := .range ranges 1,
          sorted := !isSortedRangeTable table,
          render := "" }
    else
      panic! "name table cannot be empty"
  | "Numeric_Value" =>
    let table ← mkNumericValue
    let showNumType : NumericType → String := fun
      | .decimal d => s!"NumericType.decimal ⟨{d}, by decide⟩"
      | .digit d => s!"NumericType.digit ⟨{d.val}, by decide⟩"
      | .numeric n none => s!"NumericType.numeric {n} none"
      | .numeric n (some d) => s!"NumericType.numeric ({n}) (some {d})"
    return mkRangeTable name 1 "NumericType" showNumType table
  | "Other_Alphabetic" =>
    let table := mkOtherAlphabetic
    return mkPropTable name table
  | "Other_Lowercase" =>
    let table := mkOtherLowercase
    return mkPropTable name table
  | "Other_Math" =>
    let table := mkOtherMath
    return mkPropTable name table
  | "Other_Uppercase" =>
    let table := mkOtherUppercase
    return mkPropTable name table
  | "Bidi_Mirrored" =>
    let table ← mkBidiMirrored
    return mkPropTable name table
  | "White_Space" =>
    let table := mkWhiteSpace
    return mkPropTable name table
  | "Script" =>
    let table := mkScript
    let converted := table.map fun (c₀, c₁, abbr) =>
      let sc := Script.ofAbbrev! abbr
      (c₀, c₁, sc)
    return mkRangeTable name 1 "Script" (fun sc => s!"Script.mk {hexStr sc.code}") converted
  | "Script_Extensions" =>
    let table := mkScriptExtensions
    return mkKeyTable name "ScriptExtensionsEntry" showScriptExtensionsValue table
  | "ID_Start" => pureProp name mkIDStart
  | "ID_Continue" => pureProp name mkIDContinue
  | "XID_Start" => pureProp name mkXIDStart
  | "XID_Continue" => pureProp name mkXIDContinue
  | "Dash" => pureProp name mkDash
  | "Hyphen" => pureProp name mkHyphen
  | "Quotation_Mark" => pureProp name mkQuotationMark
  | "Terminal_Punctuation" => pureProp name mkTerminalPunctuation
  | "Extender" => pureProp name mkExtender
  | "Regional_Indicator" => pureProp name mkRegionalIndicator
  | "Case_Folding" =>
    let table := mkCaseFolding
    return mkKeyTable name "CaseFolding" (fun s => s!"CaseFolding.mk {reprStr s}") table
  | "Simple_Case_Folding" =>
    let table := mkSimpleCaseFolding
    return mkPairTable name table
  | "Grapheme_Break" =>
    let table := mkGraphemeBreak
    return mkRangeTable name 1 "GraphemeClusterBreak" id table
  | "Word_Break" =>
    let table := mkWordBreak
    return mkRangeTable name 1 "WordBreak" id table
  | "Diacritic" => pureProp name mkDiacritic
  | "Sentence_Terminal" => pureProp name mkSentenceTerminal
  | "Pattern_Syntax" => pureProp name mkPatternSyntax
  | "Pattern_White_Space" => pureProp name mkPatternWhiteSpace
  | "Emoji" => pureProp name mkEmoji
  | "Emoji_Presentation" => pureProp name mkEmojiPresentation
  | "Emoji_Modifier" => pureProp name mkEmojiModifier
  | "Emoji_Modifier_Base" => pureProp name mkEmojiModifierBase
  | "Emoji_Component" => pureProp name mkEmojiComponent
  | "Extended_Pictographic" => pureProp name mkExtendedPictographic
  | "Sentence_Break" =>
    let table := mkSentenceBreak
    return mkRangeTable name 1 "SentenceBreak" id table
  | "Line_Break" =>
    let table := mkLineBreak
    return mkRangeTable name 1 "LineBreak" id table
  | "Grapheme_Base" => pureProp name mkGraphemeBase
  | "Grapheme_Extend" => pureProp name mkGraphemeExtend
  | "Uppercase" =>
    let table ← mkUppercase
    return mkPropTable name table
  | other => throw <| IO.userError s!"unknown lookup table {other}"
where
  pureProp (name : String) (table : Array (UInt32 × UInt32)) : IO GeneratedTable :=
    return mkPropTable name table

private def buildNameGenerated : IO (GeneratedTable × Array (UInt32 × UInt32 × String) × Array (Array (UInt32 × UInt32 × String))) := do
  let rows ← mkName
  let sorted := sortRangeTable rows
  let ranges := sorted.map fun (c₀, c₁, _) => (c₀, c₁)
  let (rowCount, spanCount) := Id.run <| statsData sorted
  pure ({ name := "Name", size := .ranges rowCount spanCount, rawLayout := .range (rows.map fun (c₀, c₁, _) => (c₀, c₁)) 1, layout := .range ranges 1, sorted := !isSortedRangeTable rows, render := "" }, sorted, chunkArray 512 sorted)

private def buildLineBreakGenerated : IO (GeneratedTable × Array (UInt32 × UInt32 × String) × Array (Array (UInt32 × UInt32 × String))) := do
  let rows := mkLineBreak
  let sorted := sortRangeTable rows
  let ranges := sorted.map fun (c₀, c₁, _) => (c₀, c₁)
  let (rowCount, spanCount) := Id.run <| statsData sorted
  pure ({ name := "Line_Break", size := .ranges rowCount spanCount, rawLayout := .range (rows.map fun (c₀, c₁, _) => (c₀, c₁)) 1, layout := .range ranges 1, sorted := !isSortedRangeTable rows, render := "" }, sorted, chunkArray 512 sorted)

private def buildDecompositionMappingGenerated : IO (GeneratedTable × Array (UInt32 × String) × Array (Array (UInt32 × String))) := do
  let rows ← mkDecompositionMapping
  let sorted := sortKeyTable rows
  pure ({ name := "Decomposition_Mapping", size := .rows rows.size, rawLayout := .key <| rows.map Prod.fst, layout := .key <| sorted.map Prod.fst, sorted := !isSortedKeyTable rows, render := "" }, sorted, chunkArray 512 sorted)

public def main (_args : List String) : IO UInt32 := do
  let outDir : System.FilePath := ".." / "lib" / "UnicodeBasic" / "TableLookupTables"
  IO.FS.createDirAll outDir
  for spec in MakeTablesForLookup.specs do
    if spec.fileName == "Name" then
      let nameDir : System.FilePath := outDir / "Name"
      IO.FS.createDirAll nameDir
      let generated ← buildNameGenerated
      logGeneratedTable generated.1
      let dups := duplicateReturnedStrings generated.2.1
      IO.FS.writeFile (nameDir / "DuplicatedReturnedStrings.lean") (renderDuplicatedReturnedStringsModule dups)
      for i in [0:generated.2.2.size] do
        let chunk := generated.2.2[i]!
        IO.FS.writeFile (nameDir / s!"Chunk{i}.lean") (renderNameChunkModule i chunk dups)
      IO.FS.writeFile (outDir / "Name.lean") (renderNameModule generated.2.2)
    else if spec.fileName == "Line_Break" then
      let lbDir : System.FilePath := outDir / "LineBreak"
      IO.FS.createDirAll lbDir
      let generated ← buildLineBreakGenerated
      logGeneratedTable generated.1
      for i in [0:generated.2.2.size] do
        let chunk := generated.2.2[i]!
        IO.FS.writeFile (lbDir / s!"Chunk{i}.lean") (renderLineBreakChunkModule i chunk)
      IO.FS.writeFile (outDir / "LineBreak.lean") (renderLineBreakModule generated.2.2)
    else if spec.fileName == "Decomposition_Mapping" then
      let decompDir : System.FilePath := outDir / "DecompositionMapping"
      IO.FS.createDirAll decompDir
      let generated ← buildDecompositionMappingGenerated
      logGeneratedTable generated.1
      let dups := findDuplicateChars generated.2.1
      IO.FS.writeFile (decompDir / "DuplicatedChars.lean") (renderDuplicatedCharsModule dups)
      let showDecomp : String → String := fun s =>
        let parts := s.splitOn ";"
        let tagStr := parts[0]!
        let tag := if tagStr.isEmpty then "none" else
          "(some " ++ (match tagStr with
            | "<font>" => "CompatibilityTag.font" | "<noBreak>" => "CompatibilityTag.noBreak" | "<initial>" => "CompatibilityTag.initial"
            | "<medial>" => "CompatibilityTag.medial" | "<final>" => "CompatibilityTag.final" | "<isolated>" => "CompatibilityTag.isolated"
            | "<circle>" => "CompatibilityTag.circle" | "<super>" => "CompatibilityTag.super" | "<sub>" => "CompatibilityTag.sub"
            | "<vertical>" => "CompatibilityTag.vertical" | "<wide>" => "CompatibilityTag.wide" | "<narrow>" => "CompatibilityTag.narrow"
            | "<small>" => "CompatibilityTag.small" | "<square>" => "CompatibilityTag.square" | "<fraction>" => "CompatibilityTag.fraction"
            | "<compat>" => "CompatibilityTag.compat"
            | other => panic! s!"invalid compatibility tag {other}")
          ++ ")"
        let chars := parts.drop 1 |>.map fun hex =>
          let c := Char.ofNat (ofHexString! hex.toSlice).toNat
          match findDuplicateChar dups c with
          | some dup => dup
          | none =>
            if !(c.toNat < 32 || (c.toNat >= 127 && c.toNat < 160)) && c != ' ' && c != '\u00a0' then
              toString (repr c)
            else
              s!"Char.ofNat {c.toNat}"
        let proof := match chars.length with
          | 1 => "Or.inl rfl"
          | 2 => "Or.inr (Or.inl rfl)"
          | 3 => "Or.inr (Or.inr (Or.inl rfl))"
          | 4 => "Or.inr (Or.inr (Or.inr (Or.inl rfl)))"
          | 5 => "Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))"
          | 6 => "Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))"
          | 7 => "Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))"
          | 8 => "Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))"
          | 18 => "Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))"
          | _ => "by decide"
        s!"DecompositionMapping.mk {tag} [{", ".intercalate chars}] ({proof})"
      for i in [0:generated.2.2.size] do
        let chunk := generated.2.2[i]!
        IO.FS.writeFile (decompDir / s!"Chunk{i}.lean") (renderDecompositionMappingChunkModule i chunk showDecomp)
      IO.FS.writeFile (outDir / "DecompositionMapping.lean") (renderDecompositionMappingModule generated.2.2)
    else
      if spec.fileName == "Block_Name" then
        let typesDir : System.FilePath := ".." / "lib" / "UnicodeBasic" / "Types"
        IO.FS.createDirAll typesDir
        let blockNamesTable := mkBlockName
        IO.FS.writeFile (typesDir / "BlockName.lean") (renderBlockNameTypes blockNamesTable)
      let table ← buildTable spec.fileName
      logGeneratedTable table
      let src :=
        MakeTablesForLookup.functionModuleHeader spec ++
        table.render ++
        s!"\nend Unicode.TableLookupTables.{spec.moduleName}\n"
      IO.FS.writeFile (outDir / (spec.moduleName ++ ".lean")) src
  IO.FS.writeFile (outDir.withFileName "TableLookupTables.lean") MakeTablesForLookup.renderAggregate
  return 0
