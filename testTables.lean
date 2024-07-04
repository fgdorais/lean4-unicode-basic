/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic
import UnicodeData

open Unicode

def testAlphabetic (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Lu | .Ll | .Lt | .Lm | .Lo | .Nl => true
    | _ => PropList.isOtherAlphabetic d.codeValue
  v == lookupAlphabetic d.codeValue

def testBidiClass (d : UnicodeData) : Bool :=
  d.bidiClass == lookupBidiClass d.codeValue

def testBidiMirrored (d : UnicodeData) : Bool :=
  d.bidiMirrored == lookupBidiMirrored d.codeValue

def testCanonicalCombiningClass (d : UnicodeData) : Bool :=
  d.canonicalCombiningClass == lookupCanonicalCombiningClass d.codeValue

partial def testCanonicalDecompositionMapping (d : UnicodeData) : Bool :=
  let m := lookupCanonicalDecompositionMapping d.codeValue
  let l := match d.decompositionMapping with
    | some ⟨none, l⟩ => mapping (l.map Char.val)
    | _ => [d.codeValue]
  m == l
where
  mapping : List UInt32 → List UInt32
  | [] => unreachable!
  | c :: cs =>
    let d := getUnicodeData! c
    match d.decompositionMapping with
    | some ⟨none, l⟩ => mapping <| l.map Char.val ++ cs
    | _ => c :: cs

def testCased (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Lu | .Ll | .Lt => true
    | _ =>
      PropList.isOtherLowercase d.codeValue
        || PropList.isOtherUppercase d.codeValue
  v == lookupCased d.codeValue

def testCaseMapping (d : UnicodeData) : Bool :=
  let (mu, ml, mt) := lookupCaseMapping d.codeValue
  mu == (d.uppercaseMapping.map Char.val).getD d.codeValue
    && ml == (d.lowercaseMapping.map Char.val).getD d.codeValue
      && mt == (d.titlecaseMapping.map Char.val).getD d.codeValue

def testDecompositionMapping (d : UnicodeData) : Bool :=
  d.decompositionMapping == lookupDecompositionMapping? d.codeValue

def testGeneralCategory (d : UnicodeData) : Bool :=
  d.generalCategory == lookupGeneralCategory d.codeValue

def testLowercase (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Ll => true
    | _ => PropList.isOtherLowercase d.codeValue
  v == lookupLowercase d.codeValue

def testMath (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Sm => true
    | _ => PropList.isOtherMath d.codeValue
  v == lookupMath d.codeValue

def testName (d : UnicodeData) : Bool :=
  d.characterName == lookupName d.codeValue

def testNumericValue (d : UnicodeData) : Bool :=
  d.numeric == lookupNumericValue d.codeValue

def testTitlecase (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Lt => true
    | _ => false
  v == lookupTitlecase d.codeValue

def testUppercase (d : UnicodeData) : Bool :=
  let v :=
    match d.generalCategory with
    | .Lu => true
    | _ => PropList.isOtherUppercase d.codeValue
  v == lookupUppercase d.codeValue

def testWhiteSpace (d : UnicodeData) : Bool :=
  PropList.isWhiteSpace d.codeValue == lookupWhiteSpace d.codeValue

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
        IO.println s!"Error: {t.1} {toHexStringAux d.codeValue}"
  return err
