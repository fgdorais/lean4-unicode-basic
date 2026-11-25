/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import Builders

open Unicode

/-- Directory of the UnicodeBasic library modules -/
def libDir : System.FilePath := ".."/"UnicodeBasic"

/-- `c` as a Lean hexadecimal literal -/
def hexLit (c : UInt32) : String := "0x" ++ toHexStringRaw c

/-- Write `UnicodeBasic/Internal/<module>.lean` with `rows` as the array `Internal.<name>` of
type `Array <type>`, in a `Thunk`, for the `prop` table -/
def makeTableLean (module name prop type doc : String) (imports : List String)
    (rows : Array String) : IO Unit :=
  IO.FS.withFile (libDir / "Internal" / s!"{module}.lean") .write fun file => do
    file.putStrLn "/- THIS IS A GENERATED FILE - DO NOT EDIT -/\nmodule"
    for i in imports do
      file.putStrLn s!"public import {i}"
    file.putStrLn s!"
/-! # The `{prop}` table

This module holds {doc}.
It is internal and may change at any time.
-/

namespace Unicode.Internal

-- The `Thunk` builds the array on first use, not when a program starts.
/-- The `{prop}` table (internal use only) -/
@[expose] public def {name} : Thunk (Array ({type})) := .mk fun _ => #["
    file.putStrLn <| ",\n".intercalate (rows.toList.map ("  " ++ ·))
    file.putStrLn "]"

public def main (args : List String) : IO UInt32 := do
  let args := if args != [] then args else [
    "Decomposition_Mapping",
    "Name",
    "Script_Extensions",
    "Script_Name",
    "Special_Casing"]
  let tableDir : System.FilePath := ".."/"data"
  IO.FS.createDirAll tableDir
  for arg in args do
    match arg with
    | "Alphabetic" =>
      IO.println s!"Generating table {arg}"
      let table ← mkAlphabetic
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Bidi_Class" =>
      IO.println s!"Generating table {arg}"
      let table ← mkBidiClass
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, bc) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";;" ++ bc.toAbbrev
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁ ++ ";" ++ bc.toAbbrev
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Bidi_Mirrored" =>
      IO.println s!"Generating table {arg}"
      let table ← mkBidiMirrored
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Canonical_Combining_Class" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCanonicalCombiningClass
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, cc) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", toString cc]
          else
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, toHexStringRaw c₁, toString cc]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Canonical_Decomposition_Mapping" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCanonicalDecompositionMapping
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c, l) in table do
          file.putStrLn <| toHexStringRaw c ++ ";" ++ ";".intercalate (l.map fun c => toHexStringRaw c.val)
      IO.println s!"Size: {table.size}"
    | "Case_Folding" =>
      let table := Unicode.CaseFolding.data.get
      IO.println s!"Generating table {arg}"
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c, s, f) in table do
          file.putStr <| toHexStringRaw c ++ ";"
          if s.isSome then
              file.putStr <| toHexStringRaw s.get!
          if 2 ≤ f.size  then
            file.putStrLn <| ";" ++ " ".intercalate (f.toList.map toHexStringRaw)
          else
            file.putStrLn ";"
      IO.println s!"Size: {table.size}"
    | "Case_Mapping" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCaseMapping
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, uc, lc, tc) in table  do
          if c₀ == c₁ then
            file.putStr <| toHexStringRaw c₀ ++ ";"
            if c₀ == uc then
              file.putStr <| ";"
            else
              file.putStr <| ";" ++ toHexStringRaw uc
            if c₀ == lc then
              file.putStr <| ";"
            else
              file.putStr <| ";" ++ toHexStringRaw lc
          else
            file.putStr <| ";".intercalate <| [c₀, c₁, uc, lc].map toHexStringRaw
          if uc == tc then
            file.putStrLn ";"
          else
            file.putStrLn <| ";" ++ toHexStringRaw tc
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Cased" =>
      IO.println s!"Generating table {arg}"
      let table ← mkCased
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Decomposition_Mapping" =>
      IO.println s!"Generating table {arg}"
      let table ← mkDecompositionMapping
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c, s) in table do
          file.putStrLn <| toHexStringRaw c ++ ";" ++ s
      IO.println s!"Size: {table.size}"
    | "Default_Ignorable_Code_Point" =>
      IO.println s!"Generating table {arg}"
      let table ← mkDefaultIgnorableCodePoint
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "General_Category" =>
      IO.println s!"Generating table {arg}"
      let table ← mkGC
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, v) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", toString v]
          else
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, toHexStringRaw c₁, toString v]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Lowercase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkLowercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Math" =>
      IO.println s!"Generating table {arg}"
      let table ← mkMath
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Name" =>
      IO.println s!"Generating table {arg}"
      let table ← mkName
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, n) in table do
          if c₀ == c₁ then
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", n]
          else
            file.putStrLn <| ";".intercalate [toHexStringRaw c₀, toHexStringRaw c₁, n]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Noncharacter_Code_Point" =>
      IO.println s!"Generating table {arg}"
      let table := mkNoncharacterCodePoint
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Numeric_Value" =>
      IO.println s!"Generating table {arg}"
      let table ← mkNumericValue
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, n) in table do
          match n with
          | .decimal _ => file.putStrLn <| ";".intercalate [toHexStringRaw c₀, toHexStringRaw c₁, "decimal"]
          | .digit v =>
            if c₀ == c₁ then
              file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", s!"digit {v.val}"]
            else
              let last := v.val + c₁.toNat - c₀.toNat
              file.putStrLn <| ";".intercalate [toHexStringRaw c₀, toHexStringRaw c₁, s!"digit {v.val}-{last}"]
          | .numeric v none => file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", s!"numeric {v}"]
          | .numeric v (some d) => file.putStrLn <| ";".intercalate [toHexStringRaw c₀, "", s!"numeric {v}/{d}"]
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Other_Alphabetic" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherAlphabetic
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Default_Ignorable_Code_Point" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherDefaultIgnorableCodePoint
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Lowercase" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherLowercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Math" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherMath
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other_Uppercase" =>
      IO.println s!"Generating table {arg}"
      let table := mkOtherUppercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Other" =>
      IO.println s!"Generating table {arg}"
      let table := mkOther
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁, v) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";;" ++ toString v
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁ ++ ";" ++ toString v
      IO.println s!"Size: {(statsData table).1} + {(statsData table).2}"
    | "Prepended_Concatenation_Mark" =>
      IO.println s!"Generating table {arg}"
      let table := mkPrependedConcatenationMark
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Script_Extensions" =>
      IO.println s!"Generating table {arg}"
      let table := mkScriptExtensions
      makeTableLean "ScriptExtensionsTable" "scriptExtensionsTable" arg
        "UInt32 × UInt32 × ScriptSet"
        "the code points with explicit script extensions, as ranges sorted by code point"
        ["UnicodeBasic.Types"] <| table.map fun (c₀, c₁, v) =>
          let v := ", ".intercalate (v.toList.map fun s => s!"⟨{hexLit s.code}, rfl⟩")
          s!"({hexLit c₀}, {hexLit c₁}, ⟨#[{v}], rfl⟩)"
      IO.println s!"Size: {table.size}"
    | "Script_Name" =>
      IO.println s!"Generating table {arg}"
      let table := mkScriptName
      makeTableLean "ScriptNameTable" "scriptNameTable" arg "UInt32 × String"
        "the long names of the scripts, sorted by script code" [] <|
          table.map fun (c, name) => s!"({hexLit c}, {repr name})"
      IO.println s!"Size: {table.size}"
    | "Special_Casing" =>
      let table := Unicode.SpecialCasing.data.get
      IO.println s!"Generating table {arg}"
      let rows := table.map fun (c, l, t, u) =>
        let d := getUnicodeData! c
        let sl := (d.lowercase.map Char.val).getD c
        let st := ((d.titlecase <|> d.uppercase).map Char.val).getD c
        let su := (d.uppercase.map Char.val).getD c
        let lit (m : Array UInt32) (s : UInt32) : String :=
          if m == #[s] then "[]" else "[" ++ ", ".intercalate (m.toList.map hexLit) ++ "]"
        s!"({hexLit c}, {lit l sl}, {lit t st}, {lit u su})"
      makeTableLean "SpecialCasingTable" "specialCasingTable" arg
        "UInt32 × List UInt32 × List UInt32 × List UInt32"
        ("the unconditional full case mappings (lowercase, titlecase, uppercase) that\n" ++
          "differ from the simple ones, sorted by code point, where `[]` means no difference") []
        rows
      IO.println s!"Size: {table.size}"
    | "Titlecase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkTitlecase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Uppercase" =>
      IO.println s!"Generating table {arg}"
      let table ← mkUppercase
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "Variation_Selector" =>
      IO.println s!"Generating table {arg}"
      let table := mkVariationSelector
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | "White_Space" =>
      IO.println s!"Generating table {arg}"
      let table := mkWhiteSpace
      IO.FS.withFile (tableDir/(arg ++ ".txt")) .write fun file => do
        for (c₀, c₁) in table do
          if c₀ == c₁ then
            file.putStrLn <| toHexStringRaw c₀ ++ ";"
          else
            file.putStrLn <| toHexStringRaw c₀ ++ ";" ++ toHexStringRaw c₁
      IO.println s!"Size: {(statsProp table).1} + {(statsProp table).2}"
    | _ => IO.println s!"Unknown property {arg}"
  return 0
