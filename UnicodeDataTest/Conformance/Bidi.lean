/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi
public import UnicodeDataTest.Common.Failure
public import UnicodeDataTest.Common.Types

open Unicode

namespace UnicodeDataTest.Conformance.Bidi

private def formatLevels (levels : Array (Option Nat)) : String :=
  String.intercalate " " <| levels.toList.map fun
    | some n => toString n
    | none => "x"

private def formatOrders (orders : Array Nat) : String :=
  String.intercalate " " <| orders.toList.map toString

private def formatResolution (r : Unicode.BidiResolution) : String :=
  s!"{r.paragraphLevel};{formatLevels r.resolvedLevels};{formatOrders r.visualOrder}"

private def formatLevelOrder (levels : Array (Option Nat)) (orders : Array Nat) : String :=
  s!"{formatLevels levels};{formatOrders orders}"

private def runCharacterCase (ctx : Unicode.BidiContext) (tc : UnicodeDataTest.BidiCharacterTestCase) : Option UnicodeDataTest.Common.Failure := do
  let expected : Unicode.BidiResolution := {
    paragraphLevel := tc.paragraphLevel
    resolvedLevels := tc.resolvedLevels
    visualOrder := tc.visualOrder
  }
  match Unicode.resolveBidiText ctx tc.input tc.paragraphDirection with
  | .error raw =>
      some {
        file := "BidiCharacterTest.txt"
        line := tc.line
        expected := formatResolution expected
        actual := s!"{raw}"
        comment := tc.comment
      }
  | .ok out =>
      if out ≠ expected then
        some {
          file := "BidiCharacterTest.txt"
          line := tc.line
          expected := formatResolution expected
          actual := formatResolution out
          comment := tc.comment
        }
      else
        none

private def directionsOfMask (mask : Nat) : Array Unicode.BidiParagraphDirection := Id.run do
  let mut out := #[]
  if mask.testBit 0 then
    out := out.push .autoLtr
  if mask.testBit 1 then
    out := out.push .ltr
  if mask.testBit 2 then
    out := out.push .rtl
  return out

private def runBidiTestCase (ctx : Unicode.BidiContext) (tc : UnicodeDataTest.BidiTestCase) : Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  let expected : Unicode.BidiResolution := {
    paragraphLevel := 0
    resolvedLevels := tc.expectedLevels
    visualOrder := tc.expectedReorder
  }
  for dir in directionsOfMask tc.paragraphMask do
    match Unicode.resolveBidiClasses ctx tc.input dir with
    | .error raw =>
      failures := failures.push {
          file := "BidiTest.txt"
          line := tc.line
          expected := formatLevelOrder expected.resolvedLevels expected.visualOrder
          actual := s!"{raw}"
          comment := tc.comment
        }
    | .ok out =>
        if out.resolvedLevels ≠ tc.expectedLevels || out.visualOrder ≠ tc.expectedReorder then
          failures := failures.push {
            file := "BidiTest.txt"
            line := tc.line
            expected := formatLevelOrder expected.resolvedLevels expected.visualOrder
            actual := formatLevelOrder out.resolvedLevels out.visualOrder
            comment := tc.comment
          }
  return failures

public def runConformance
    (characterCases : Array UnicodeDataTest.BidiCharacterTestCase)
    (bidiCases : Array UnicodeDataTest.BidiTestCase) :
    Array UnicodeDataTest.Common.Failure := Id.run do
  match Unicode.bidiInit "data/ucd/core/" with
  | .error err =>
      return #[{
        file := "BidiInit"
        line := 0
        expected := "successful bidi bridge initialization"
        actual := s!"{err}"
      }]
  | .ok ctx =>
      let mut failures := #[]
      for tc in characterCases do
        match runCharacterCase ctx tc with
        | some failure => failures := failures.push failure
        | none => continue
      for tc in bidiCases do
        failures := failures ++ runBidiTestCase ctx tc
      return failures

end UnicodeDataTest.Conformance.Bidi
