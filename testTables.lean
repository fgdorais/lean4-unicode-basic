/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic
import UnicodeData

open Unicode

def testAlphabetic (d : UnicodeData) : Bool :=
  let v :=
    if d.gc ∈ [.Lu, .Ll, .Lt, .Lm, .Lo, .Nl] then true
    else PropList.isOtherAlphabetic d.code
  v == lookupAlphabetic d.code

def testBidiClass (d : UnicodeData) : Bool :=
  d.bidi == lookupBidiClass d.code

def testBidiMirrored (d : UnicodeData) : Bool :=
  d.bidiMirrored == lookupBidiMirrored d.code

def testCanonicalCombiningClass (d : UnicodeData) : Bool :=
  d.cc == lookupCanonicalCombiningClass d.code

partial def testCanonicalDecompositionMapping (d : UnicodeData) : Bool :=
  let m := lookupCanonicalDecompositionMapping d.code
  let l := match d.decomp with
    | some ⟨none, l⟩ => mapping (l.map Char.val)
    | _ => [d.code]
  m == l
where
  mapping : List UInt32 → List UInt32
  | [] => unreachable!
  | c :: cs =>
    let d := getUnicodeData! c
    match d.decomp with
    | some ⟨none, l⟩ => mapping <| l.map Char.val ++ cs
    | _ => c :: cs

def testCased (d : UnicodeData) : Bool :=
  let v :=
    match d.gc with
    | .Lu | .Ll | .Lt => true
    | _ =>
      PropList.isOtherLowercase d.code
        || PropList.isOtherUppercase d.code
  v == lookupCased d.code

def testCaseMapping (d : UnicodeData) : Bool :=
  let (mu, ml, mt) := lookupCaseMapping d.code
  mu == (d.uppercase.map Char.val).getD d.code
    && ml == (d.lowercase.map Char.val).getD d.code
      && mt == (d.titlecase.map Char.val).getD d.code

def testDecompositionMapping (d : UnicodeData) : Bool :=
  d.decomp == lookupDecompositionMapping? d.code

def testGeneralCategory (d : UnicodeData) : Bool :=
  d.gc == lookupGC d.code

def testLowercase (d : UnicodeData) : Bool :=
  let v :=
    match d.gc with
    | .Ll => true
    | _ => PropList.isOtherLowercase d.code
  v == lookupLowercase d.code

def testMath (d : UnicodeData) : Bool :=
  let v :=
    match d.gc with
    | .Sm => true
    | _ => PropList.isOtherMath d.code
  v == lookupMath d.code

def testName (d : UnicodeData) : Bool :=
  d.name == lookupName d.code

def testNumericValue (d : UnicodeData) : Bool :=
  d.numeric == lookupNumericValue d.code

def testTitlecase (d : UnicodeData) : Bool :=
  let v :=
    match d.gc with
    | .Lt => true
    | _ => false
  v == lookupTitlecase d.code

def testUppercase (d : UnicodeData) : Bool :=
  let v :=
    match d.gc with
    | .Lu => true
    | _ => PropList.isOtherUppercase d.code
  v == lookupUppercase d.code

def testWhiteSpace (d : UnicodeData) : Bool :=
  PropList.isWhiteSpace d.code == lookupWhiteSpace d.code

def tests : Array (String × (UnicodeData → Bool)) := #[
  ("Bidi_Class", testBidiClass),
  ("Alphabetic", testAlphabetic),
  ("Bidi_Class", testBidiClass),
  ("Bidi_Mirrored", testBidiMirrored),
  ("Canonical_Combining_Class", testCanonicalCombiningClass),
  ("Canonical_Decomposition_Mapping", testCanonicalDecompositionMapping),
  ("Case_Mapping", testCaseMapping),
  ("Cased", testCased),
  ("Decomposition_Mapping", testDecompositionMapping),
  ("Lowercase", testLowercase),
  ("Math", testMath),
  ("Name", testName),
  ("Titlecase", testTitlecase),
  ("Uppercase", testUppercase),
  ("Numeric_Value", testNumericValue),
  ("General_Category", testGeneralCategory),
  ("White_Space", testWhiteSpace)]

def main (args : List String) : IO UInt32 := do
  let args := if args.isEmpty then tests.map Prod.fst else args.toArray
  let stream : UnicodeDataStream := {}
  let mut err : UInt32 := 0
  for d in stream do
    for t in tests do
      if t.1 ∈ args && !t.2 d then
        err := 1
        IO.println s!"Error: {t.1} {toHexStringAux d.code}"
  return err
