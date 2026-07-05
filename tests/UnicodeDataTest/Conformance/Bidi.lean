/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi
public import UnicodeDataTest.Conformance.Data.BidiCharacterTest
public import UnicodeDataTest.Conformance.Data.BidiTest
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

private def expectResolution
    (name : String) (line : Nat)
    (expected actual : Unicode.BidiResolution) :
    Option UnicodeDataTest.Common.Failure :=
  if actual == expected then
    none
  else
    some {
      file := "BidiRegression"
      line
      expected := formatResolution expected
      actual := formatResolution actual
      comment := some name
    }

private def expectArray [BEq α] [Repr α]
    (name : String) (line : Nat)
    (expected actual : Array α) :
    Option UnicodeDataTest.Common.Failure :=
  if actual == expected then
    none
  else
    some {
      file := "BidiRegression"
      line
      expected := reprStr expected
      actual := reprStr actual
      comment := some name
    }

private def pushFailure?
    (failures : Array UnicodeDataTest.Common.Failure)
    (failure? : Option UnicodeDataTest.Common.Failure) :
    Array UnicodeDataTest.Common.Failure :=
  match failure? with
  | some f => failures.push f
  | none => failures

private def runFocusedRegressions : Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]

  failures := pushFailure? failures <| expectResolution "empty input" 1
    { paragraphLevel := 0, resolvedLevels := #[], visualOrder := #[] }
    (Unicode.resolveBidiClasses #[] .ltr)

  failures := pushFailure? failures <| expectResolution "simple rtl visual order" 2
    { paragraphLevel := 0, resolvedLevels := #[some 1, some 1], visualOrder := #[1, 0] }
    (Unicode.resolveBidiClasses #[.rightToLeft, .rightToLeft] .ltr)

  failures := pushFailure? failures <| expectResolution "auto paragraph first strong rtl" 3
    { paragraphLevel := 1, resolvedLevels := #[some 1, some 1], visualOrder := #[1, 0] }
    (Unicode.resolveBidiClasses #[.otherNeutral, .rightToLeft] .autoLtr)

  failures := pushFailure? failures <| expectResolution "x9 deleted control with surrounding rtl" 4
    { paragraphLevel := 0, resolvedLevels := #[some 1, none, some 1], visualOrder := #[2, 0] }
    (Unicode.resolveBidiClasses #[.rightToLeft, .popDirectionalFormat, .arabicLetter] .ltr)

  failures := pushFailure? failures <| expectResolution "canonical paired bracket equivalents" 5
    { paragraphLevel := 1, resolvedLevels := #[some 2, some 2, some 2, some 2, some 2, some 2, some 2], visualOrder := #[0, 1, 2, 3, 4, 5, 6] }
    (Unicode.resolveBidiText #[0x0061, 0x0020, 0x2329, 0x0062, 0x002E, 0x0031, 0x232A] .rtl)

  let text := #[0x0061, 0x05D0, 0x0062]
  let resolved := Unicode.resolveBidiText text .ltr
  failures := pushFailure? failures <| expectArray "visual reorder helper" 6
    #[0x0061, 0x05D0, 0x0062]
    (Unicode.reorderBidiText text resolved)

  failures := pushFailure? failures <| expectArray "logical run helper" 7
    #[{ start := 0, stop := 1, level := 0 : Unicode.BidiRun },
      { start := 1, stop := 2, level := 1 : Unicode.BidiRun },
      { start := 2, stop := 3, level := 0 : Unicode.BidiRun }]
    (Unicode.bidiRuns resolved)

  failures := pushFailure? failures <| expectArray "string codepoint helper" 8
    #[0x0061, 0x05D0]
    (Unicode.bidiCodepointsOfString "aא")

  return failures

private def runCharacterCase (tc : UnicodeDataTest.Conformance.Data.BidiCharacterTest.BidiCharacterTestCase) : Option UnicodeDataTest.Common.Failure := do
  let expected : Unicode.BidiResolution := {
    paragraphLevel := tc.paragraphLevel
    resolvedLevels := tc.resolvedLevels
    visualOrder := tc.visualOrder
  }
  let out := Unicode.resolveBidiText tc.input tc.paragraphDirection
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

private def runBidiTestCase (tc : UnicodeDataTest.Conformance.Data.BidiTest.BidiTestCase) : Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  let expected : Unicode.BidiResolution := {
    paragraphLevel := 0
    resolvedLevels := tc.expectedLevels
    visualOrder := tc.expectedReorder
  }
  for dir in directionsOfMask tc.paragraphMask do
    let out := Unicode.resolveBidiClasses tc.input dir
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
    (characterCases : Array UnicodeDataTest.Conformance.Data.BidiCharacterTest.BidiCharacterTestCase)
    (bidiCases : Array UnicodeDataTest.Conformance.Data.BidiTest.BidiTestCase) :
    Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  for tc in characterCases do
    match runCharacterCase tc with
    | some failure => failures := failures.push failure
    | none => continue
  for tc in bidiCases do
    failures := failures ++ runBidiTestCase tc
  failures := failures ++ runFocusedRegressions
  return failures

end UnicodeDataTest.Conformance.Bidi
