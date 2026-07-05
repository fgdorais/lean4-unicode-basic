/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic
public import UnicodeBasic.Hangul
import UnicodeData.Basic
import UnicodeData.Core.CompositionExclusions
public import UnicodeDataTest.Conformance.Data.NormalizationTest
public import UnicodeDataTest.Common.Failure
public import UnicodeDataTest.Common.Types

open Unicode

namespace UnicodeDataTest.Conformance.Normalization

private def decomposeHangul (c : UInt32) : Option (List UInt32) :=
  match Hangul.getSyllable? c with
  | none => none
  | some s =>
    match s.getTChar? with
    | some t => some [s.getLChar.val, s.getVChar.val, t.val]
    | none => some [s.getLChar.val, s.getVChar.val]

private partial def decomposeRec (compat : Bool) (c : UInt32) : List UInt32 :=
  match decomposeHangul c with
  | some xs => xs.flatMap (decomposeRec compat)
  | none =>
      match lookupDecompositionMapping? c with
      | some { tag, mapping, .. } =>
          if tag.isSome && !compat then
            [c]
          else
            (mapping.map (fun ch => ch.val)).flatMap (decomposeRec compat)
      | none => [c]

private def decomposeSeq (compat : Bool) (xs : Array UInt32) : Array UInt32 :=
  xs.toList.flatMap (decomposeRec compat) |>.toArray

private def insertByCCC (c : UInt32) (tail : List UInt32) : List UInt32 :=
  match tail with
  | [] => [c]
  | x :: xs =>
      if lookupCanonicalCombiningClass c < lookupCanonicalCombiningClass x then
        c :: tail
      else
        x :: insertByCCC c xs

private def reorderCanonical (xs : Array UInt32) : Array UInt32 := Id.run do
  let mut out : List UInt32 := []
  let mut segment : List UInt32 := []
  let mut hasStarter := false
  for c in xs do
    if lookupCanonicalCombiningClass c == 0 then
      out := out ++ segment
      segment := [c]
      hasStarter := true
    else
      match segment with
      | [] =>
          segment := [c]
          hasStarter := false
      | _ =>
          if hasStarter then
            match segment with
            | s :: tail => segment := s :: insertByCCC c tail
            | [] => segment := [c]
          else
            segment := insertByCCC c segment
  out := out ++ segment
  return out.toArray

private def composeHangul? (a b : UInt32) : Option UInt32 :=
  let aN := a.toNat
  let bN := b.toNat
  let lBase := Hangul.baseL.toNat
  let vBase := Hangul.baseV.toNat
  let tBase := Hangul.baseT.toNat
  let sBase := Hangul.Syllable.base.toNat
  let lCount := Hangul.sizeL
  let vCount := Hangul.sizeV
  let tCount := Hangul.sizeT
  if aN >= lBase && aN < lBase + lCount && bN >= vBase && bN < vBase + vCount then
    some <| UInt32.ofNat <| sBase + ((aN - lBase) * vCount + (bN - vBase)) * tCount
  else if bN > tBase && bN < tBase + tCount then
    match Hangul.getSyllable? a with
    | some s =>
        if s.toT.val == 0 then
          some <| UInt32.ofNat <| aN + (bN - tBase)
        else
          none
    | none => none
  else
    none

private def composePairs : Array ((UInt32 × UInt32) × UInt32) := Id.run do
  let mut out := #[]
  for d in UnicodeData.data do
    match d.decomp with
    | some { tag := none, mapping := [a, b], .. } =>
        if !Unicode.CompositionExclusions.data.contains d.code then
          out := out.push ((a.val, b.val), d.code)
    | _ => continue
  return out

private def composePair? (a b : UInt32) : Option UInt32 :=
  match composeHangul? a b with
  | some c => some c
  | none =>
      let rec go (i : Nat) : Option UInt32 :=
        if i < composePairs.size then
          let entry := composePairs[i]!
          if entry.1.1 == a && entry.1.2 == b then
            some entry.2
          else
            go (i + 1)
        else
          none
      go 0

private def composeSeq (xs : Array UInt32) : Array UInt32 := Id.run do
  if xs.isEmpty then
    return xs
  let first := xs[0]!
  let mut out := #[first]
  let mut starter : Option Nat := if lookupCanonicalCombiningClass first == 0 then some 0 else none
  let mut lastCCC : Nat := lookupCanonicalCombiningClass first
  for i in [1:xs.size] do
    let c := xs[i]!
    let ccc := lookupCanonicalCombiningClass c
    match starter with
    | some sIdx =>
        let s := out[sIdx]!
        match composePair? s c with
        | some composed =>
            if (ccc == 0 && lastCCC == 0) || (ccc != 0 && lastCCC < ccc) then
              out := out.set! sIdx composed
            else
              out := out.push c
              if ccc == 0 then
                starter := some (out.size - 1)
                lastCCC := 0
              else
                lastCCC := ccc
        | none =>
            if ccc == 0 then
              out := out.push c
              starter := some (out.size - 1)
              lastCCC := 0
            else if lastCCC < ccc then
              out := out.push c
              lastCCC := ccc
            else
              out := out.push c
              lastCCC := ccc
    | none =>
        if ccc == 0 then
          out := out.push c
          starter := some (out.size - 1)
          lastCCC := 0
        else
          out := out.push c
          lastCCC := ccc
  return out

private def normalize (compat compose : Bool) (xs : Array UInt32) : Array UInt32 :=
  let decomp := reorderCanonical <| decomposeSeq compat xs
  if compose then composeSeq decomp else decomp

public def nfd (xs : Array UInt32) : Array UInt32 := normalize false false xs
public def nfkd (xs : Array UInt32) : Array UInt32 := normalize true false xs
public def nfc (xs : Array UInt32) : Array UInt32 := normalize false true xs
public def nfkc (xs : Array UInt32) : Array UInt32 := normalize true true xs

public def runConformance (file : String) (cases : Array UnicodeDataTest.Conformance.Data.NormalizationTest.NormalizationTestCase) : Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  for tc in cases do
    let aNfc := nfc tc.source
    let aNfd := nfd tc.source
    let aNfkc := nfkc tc.source
    let aNfkd := nfkd tc.source
    if aNfc != tc.nfc then
      failures := failures.push { file := file, line := tc.line, expected := s!"{tc.nfc}", actual := s!"{aNfc}", comment := tc.comment }
    if aNfd != tc.nfd then
      failures := failures.push { file := file, line := tc.line, expected := s!"{tc.nfd}", actual := s!"{aNfd}", comment := tc.comment }
    if aNfkc != tc.nfkc then
      failures := failures.push { file := file, line := tc.line, expected := s!"{tc.nfkc}", actual := s!"{aNfkc}", comment := tc.comment }
    if aNfkd != tc.nfkd then
      failures := failures.push { file := file, line := tc.line, expected := s!"{tc.nfkd}", actual := s!"{aNfkd}", comment := tc.comment }
  return failures

end UnicodeDataTest.Conformance.Normalization
