/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic
import UnicodeData.Core.DerivedCoreProperties
public import UnicodeDataTest.Common.Failure
public import UnicodeDataTest.Common.Types

open Unicode

namespace UnicodeDataTest.Auxiliary.Grapheme

private def gcb (c : UInt32) : MaybeGraphemeClusterBreak :=
  lookupGraphemeClusterBreak c

private def isIndicConsonant (c : UInt32) : Bool :=
  DerivedCoreProperties.isIndicConjunctBreakConsonant c

private def isIndicLinker (c : UInt32) : Bool :=
  DerivedCoreProperties.isIndicConjunctBreakLinker c

private def isControlLike (c : UInt32) : Bool :=
  match gcb c with
  | .nonOther .control | .nonOther .cr | .nonOther .lf => true
  | _ => false

private def prevNonExtendIndex (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    if gcb xs[j]! != .nonOther .extend then
      return some j
  return none

private def gb11Before? (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  if !lookupExtendedPictographic xs[i]! then
    return false
  match prevNonExtendIndex xs i with
  | some j1 =>
      if gcb xs[j1]! != .nonOther .zwj then
        return false
      match prevNonExtendIndex xs j1 with
      | some j0 => return lookupExtendedPictographic xs[j0]!
      | none => return false
  | none => false

private def gb9cBefore? (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  if !isIndicConsonant xs[i]! then
    return false
  let mut j := i
  let mut seenLinker := false
  while j > 0 do
    j := j - 1
    let c := xs[j]!
    if isIndicLinker c then
      seenLinker := true
      continue
    else if gcb c == .nonOther .extend || gcb c == .nonOther .zwj then
      continue
    else
      return seenLinker && isIndicConsonant c
  return false

private def shouldBreakBefore (xs : Array UInt32) (i : Nat) (riRun : Nat) : Bool := Id.run do
  if i = 0 then
    true
  else
    let prev := xs[i - 1]!
    let curr := xs[i]!
    let prevG := gcb prev
    let currG := gcb curr
    if prevG == .nonOther .cr && currG == .nonOther .lf then
      false
    else if isControlLike prev || isControlLike curr then
      true
    else if prevG == .nonOther .l && (currG == .nonOther .l || currG == .nonOther .v || currG == .nonOther .lv || currG == .nonOther .lvt) then
      false
    else if (prevG == .nonOther .lv || prevG == .nonOther .v) && (currG == .nonOther .v || currG == .nonOther .t) then
      false
    else if (prevG == .nonOther .lvt || prevG == .nonOther .t) && currG == .nonOther .t then
      false
    else if currG == .nonOther .extend || currG == .nonOther .zwj || currG == .nonOther .spacingMark then
      false
    else if prevG == .nonOther .prepend then
      false
    else if currG == .nonOther .regionalIndicator && prevG == .nonOther .regionalIndicator && riRun % 2 == 1 then
      false
    else if gb9cBefore? xs i then
      false
    else if gb11Before? xs i then
      false
    else
      true

/-- Segment grapheme cluster boundaries, including the start and end positions. -/
public def segmentGraphemeBoundaries (xs : Array UInt32) : Array Nat := Id.run do
  if xs.isEmpty then
    return #[0]
  let mut out := #[0]
  let mut riRun := if gcb xs[0]! == .nonOther .regionalIndicator then 1 else 0
  for i in [1:xs.size] do
    if shouldBreakBefore xs i riRun then
      out := out.push i
      riRun := if gcb xs[i]! == .nonOther .regionalIndicator then 1 else 0
    else
      let curr := gcb xs[i]!
      if curr == .nonOther .regionalIndicator then
        riRun := riRun + 1
      else
        riRun := 0
  out := out.push xs.size
  return out

/-- Check grapheme-break conformance against the parsed cases. -/
public def runConformance (file : String) (cases : Array UnicodeDataTest.BreakTestCase) : Array UnicodeDataTest.Common.Failure :=
  Id.run do
    let mut failures := #[]
    for tc in cases do
      let actual := segmentGraphemeBoundaries tc.codepoints
      if actual != tc.boundaries then
        failures := failures.push {
          file := file
          line := tc.line
          expected := s!"{tc.boundaries}"
          actual := s!"{actual}"
          comment := tc.comment
        }
    return failures

end UnicodeDataTest.Auxiliary.Grapheme
