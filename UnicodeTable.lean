/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic

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

def mkBidiClass : IO <| Array (UInt32 × UInt32 × BidiClass) := do
  let mut t := #[]
  for d in UnicodeData.data do
    match t.back? with
    | some (c₀, c₁, bc) =>
      if d.codeValue = c₁ + 1 && d.bidiClass == bc then
        t := t.pop.push (c₀, c₁+1, bc)
      else
        t := t.push (d.codeValue, d.codeValue, d.bidiClass)
    | none =>
      t := t.push (d.codeValue, d.codeValue, d.bidiClass)
  return t

def mkBidiMirrored : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for d in UnicodeData.data do
    if d.bidiMirrored then
      match t.back? with
      | some (c₀, c₁) =>
        if d.codeValue == c₁ + 1 then
          t := t.pop.push (c₀, d.codeValue)
        else
          t := t.push (d.codeValue, d.codeValue)
      | none =>
        t := t.push (d.codeValue, d.codeValue)
  return t

def mkCanonicalCombiningClass : IO <| Array (UInt32 × UInt32 × Nat) := do
  let mut t := #[]
  for d in UnicodeData.data do
    if d.canonicalCombiningClass > 0 then
      match t.back? with
      | some (c₀, c₁, cc) =>
        if t.size != 0 && d.codeValue == c₁ + 1 && d.canonicalCombiningClass == cc then
          t := t.pop.push (c₀, c₁+1, cc)
        else
          t := t.push (d.codeValue, d.codeValue, d.canonicalCombiningClass)
      | none =>
        t := t.push (d.codeValue, d.codeValue, d.canonicalCombiningClass)
  return t

def mkCanonicalDecomposition : IO <| Array (UInt32 × List UInt32) := do
  let mut t := #[]
  for data in UnicodeData.data do
    match data.decompositionMapping with
    | some ⟨none, l⟩ =>
      t := t.push (data.codeValue, l.map Char.val)
    | _ => continue
  return t

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
    match data.decompositionMapping with
    | some ⟨none, l⟩ =>
      t := t.push (data.codeValue, " ".intercalate <| l.map (toHexStringAux <| Char.val .))
    | some ⟨some k, l⟩ =>
      t := t.push (data.codeValue, s!"{k} " ++ " ".intercalate (l.map (toHexStringAux <| Char.val ·)))
    | _ => continue
  return t

def mkGeneralCategory : IO <| Array (UInt32 × UInt32 × GeneralCategory) := do
  let mut t := #[(0,0,GeneralCategory.Cc)]
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
    let c := data.codeValue
    let k := data.generalCategory
    if data.characterName.takeRight 8 == ", First>" then
      t := t.push (c, c, k)
    else if data.characterName.takeRight 7 == ", Last>" then
      match t.back with
      | (c₀, _, k) =>
        t := t.pop.push (c₀, c, k)
    else
      let k :=
        if k == .Lu && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Ll
          then .LC
          else k
        else if k == .Ll && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Lu
          then .LC
          else k
        else if k == .Ps && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Pe
          then .PG
          else k
        else if k == .Pe && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Ps
          then .PG
          else k
        else if k == .Pi && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Pf
          then .PQ
          else k
        else if k == .Pf && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Pi
          then .PQ
          else k
        else k
      match t.back with
      | (c₀, c₁, k₁) =>
        if c == c₁ + 1 && k == k₁ then
          t := t.pop.push (c₀, c, k)
        else
          t := t.push (c, c, k)
  return t

def mkName : IO <| Array (UInt32 × UInt32 × String) := do
  let mut t := #[(0,0,"<control>")]
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
    let c := data.codeValue
    let n := data.characterName.toString
    if n.takeRight 8 == ", First>" then
      if "<CJK Ideograph Extension".isPrefixOf n then
        t := t.push (c, c, "<CJK Unified Ideograph>")
      else
        t := t.push (c, c, n.dropRight 8 ++ ">")
    else if n.takeRight 7 == ", Last>" then
      match t.back with
      | (c₀, _, n) =>
        t := t.pop.push (c₀, c, n)
    else if "CJK COMPATIBILITY IDEOGRAPH-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<CJK Compatibility Ideograph>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<CJK Compatibility Ideograph>")
    else if "KHITAN SMALL SCRIPT CHARACTER-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Khitan Small Script Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Khitan Small Script Character>")
    else if "NUSHU CHARACTER-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Nushu Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Nushu Character>")
    else if "TANGUT COMPONENT-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Tangut Component>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Tangut Component>")
    else
      match t.back with
      | (c₀, c₁, n₀) =>
        if c == c₁ + 1 && n == n₀ then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, n)
  return t

def mkNumericValue : IO <| Array (UInt32 × UInt32 × NumericType) := do
  let mut t := #[]
  for d in UnicodeData.data do
    match d.numeric with
    | some (.decimal 0) =>
      t := t.push (d.codeValue, d.codeValue + 10, .decimal 0)
    | some (.digit v) =>
      match t.back with
      | (c₀, c₁, n@(NumericType.digit x)) =>
        let last := x.val + c₁.val - c₀.val
        if d.codeValue == c₁ + 1 && v.val == last + 1 then
          t := t.pop.push (c₀, d.codeValue, n)
        else
          t := t.push (d.codeValue, d.codeValue, .digit v)
      | _ =>
        t := t.push (d.codeValue, d.codeValue, .digit v)
    | some n@(.numeric _ _) =>
      t := t.push (d.codeValue, d.codeValue, n)
    | _ => continue
  return t

def mkNoncharacterCodePoint : Array (UInt32 × UInt32) :=
  PropList.data.noncharacterCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

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

def mkAlphabetic : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun d =>
    if d.2.2 ∈ [.LC, .Ll, .Lu, .Lt, .Lm, .Lo, .Nl] then
      some (d.1, d.2.1)
    else
      none
  return mergeProp #[t, mkOtherAlphabetic, mkOtherLowercase, mkOtherUppercase]

def mkCased : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun d =>
    if d.2.2 ∈ [.LC, .Ll, .Lu, .Lt] then
      some (d.1, d.2.1)
    else
      none
  return mergeProp #[t, mkOtherLowercase, mkOtherUppercase]

def mkMath : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun
    | (c₀, c₁, .Sm) => some (c₀, c₁)
    | _ => none
  return mergeProp #[t, mkOtherMath]

def mkLowercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Ll) =>
      t := t.push (c₀, c₁)
    | (c₀, c₁, .LC) =>
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 != 0 then t := t.push (c.toUInt32, c.toUInt32)
    | _ => continue
  return mergeProp #[t, mkOtherLowercase]

def mkTitlecase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Lt) =>
      t := t.push (c₀, c₁)
    | _ => continue
  return t

def mkUppercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Lu) =>
      t := t.push (c₀, c₁)
    | (c₀, c₁, .LC) =>
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 == 0 then t := t.push (c.toUInt32, c.toUInt32)
    | _ => continue
  return mergeProp #[t, mkOtherUppercase]

def mkWhiteSpace : Array (UInt32 × UInt32) :=
  PropList.data.whiteSpace.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def main (args : List String) : IO UInt32 := do
  let args := if args != [] then args else [
    "Alphabetic",
    "Bidi_Class",
    "Bidi_Mirrored",
    "Canonical_Combining_Class",
    "Case_Mapping",
    "Cased",
    "Lowercase",
    "Math",
    "Name",
    "Titlecase",
    "Uppercase",
    "Numeric_Value",
    "General_Category",
    "White_Space"]
  let tableDir : System.FilePath := "."/"data"/"table"
  IO.FS.createDirAll tableDir
  for arg in args do
    match arg with
    | "Alphabetic" =>
      IO.println s!"Generating table {arg}"
      let table ← mkAlphabetic
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Bidi_Class" =>
      IO.println s!"Generating table {arg}"
      let table ← mkBidiClass
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, bc) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";;" ++ bc.toAbbrev
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁ ++ ";" ++ bc.toAbbrev
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Bidi_Mirrored" =>
      IO.println s!"Generating table {arg}"
      let table ← mkBidiMirrored
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Canonical_Combining_Class" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCanonicalCombiningClass
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, cc) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", toString cc]
          else
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, toHexStringAux c₁, toString cc]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Case_Mapping" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCaseMapping
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, uc, lc, tc) in table  do
          if c₀ == c₁ then
            file.putStr <| toHexStringAux c₀ ++ ";"
            if c₀ == uc then
              file.putStr <| ";"
            else
              file.putStr <| ";" ++ toHexStringAux uc
            if c₀ == lc then
              file.putStr <| ";"
            else
              file.putStr <| ";" ++ toHexStringAux lc
          else
            file.putStr <| ";".intercalate <| [c₀, c₁, uc, lc].map toHexStringAux
          if uc == tc then
            file.putStrLn ";"
          else
            file.putStrLn <| ";" ++ toHexStringAux tc
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Cased" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCased
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Decomposition_Mapping" =>
      IO.println s!"Generating table {arg}"
      let table ← mkDecompositionMapping
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c, s) in table do
          file.putStrLn <| ";".intercalate [toHexStringAux c, s]
      IO.println s!"Size: {table.size}"
    | "General_Category" =>
      IO.println s!"Generating table {arg}"
      let table ← mkGeneralCategory
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, gc) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", gc.toAbbrev]
          else
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, toHexStringAux c₁, gc.toAbbrev]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Lowercase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkLowercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Math" =>
      IO.println s!"Generating table {arg}"
      let table ← mkMath
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Name" =>
      IO.println s!"Generating table {arg}"
      let table ← mkName
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, n) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", n]
          else
            file.putStrLn <| ";".intercalate [toHexStringAux c₀, toHexStringAux c₁, n]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Noncharacter_Code_Point" =>
      IO.println s!"Generating table {arg}"
      let table := mkNoncharacterCodePoint
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Numeric_Value" =>
      IO.println s!"Generating table {arg}"
      let table ← mkNumericValue
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, n) in table do
          match n with
          | .decimal _ => file.putStrLn <| ";".intercalate [toHexStringAux c₀, toHexStringAux c₁, "decimal"]
          | .digit v =>
            if c₀ == c₁ then
              file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", s!"digit {v.val}"]
            else
              let last := v.val + c₁.toNat - c₀.toNat
              file.putStrLn <| ";".intercalate [toHexStringAux c₀, toHexStringAux c₁, s!"digit {v.val}-{last}"]
          | .numeric v none => file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", s!"numeric {v}"]
          | .numeric v (some d) => file.putStrLn <| ";".intercalate [toHexStringAux c₀, "", s!"numeric {v}/{d}"]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Other_Alphabetic" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherAlphabetic
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Lowercase" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherLowercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Math" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherMath
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Uppercase" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherUppercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Titlecase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkTitlecase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Uppercase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkUppercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "White_Space" =>
      IO.println s!"Generating table {arg}"
      let table := mkWhiteSpace
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringAux c₀ ++ ";"
          else
            file.putStrLn <| toHexStringAux c₀ ++ ";" ++ toHexStringAux c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | _ => IO.println s!"Unknown property {arg}"
  return 0
