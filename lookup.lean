/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic
import UnicodeData

open Unicode

def main (args : List String) : IO Unit := do
  for a in args do
    match getArg? a with
    | none => IO.println s!"invalid argument: {a}"
    | some n =>
      match Unicode.getUnicodeData? n with
      | none => IO.println s!"invalid code point: {a}"
      | some data =>
        IO.println s!"Code Value ...........: {Unicode.toHexString data.code} (decimal {data.code})"
        IO.println s!"Character Name .......: {data.name.copy}"
        IO.println s!"General Category .....: {data.gc}"
        IO.println s!"Combining Class ......: {data.cc}"
        IO.println s!"Bidi Class ...........: {data.bidi.toAbbrev}"
        IO.println s!"Bidi Mirrored ........: {data.bidiMirrored}"
        match data.decomp with
        | some ⟨none, m⟩ =>
        IO.println s!"Decomposition Mapping : \"{String.ofList m}\" (canonical)"
        | some ⟨some t, m⟩ => IO.println s!"Decomposition Mapping : {t} \"{String.ofList m}\" (compatibility)"
        | none => pure ()
        match data.numeric with
        | some (.decimal d) =>
        IO.println s!"Numeric Value ........: \"{d}\" (decimal)"
        | some (.digit d) => IO.println s!"Numeric Value ........: \"{d}\" (digit)"
        | some (.numeric n none) => IO.println s!"Numeric Value ........: \"{n}\" (numeric)"
        | some (.numeric n (some d)) => IO.println s!"Numeric Value ........: \"{n}/{d}\" (numeric)"
        | none => pure ()
        match data.uppercase with
        | some l => IO.println s!"Uppercase Mapping ....: \'{l}\'"
        | none => pure ()
        match data.lowercase with
        | some l => IO.println s!"Lowercase Mapping ....: \'{l}\'"
        | none => pure ()
        match data.titlecase with
        | some l => IO.println s!"Titlecase Mapping ....: \'{l}\'"
        | none => pure ()

where

  getArg? (a : String) : Option UInt32 := do
    if a.take 2 == "U+".toSlice then
      Unicode.ofHexString? a
    else if a.length == 1 then
      Char.val <$> String.Pos.Raw.get? a 0
    else
      Nat.toUInt32 <$> a.toNat?
