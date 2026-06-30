/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic
public import UnicodeDataTest.Common.Failure
public import UnicodeDataTest.Common.Types

open Unicode

namespace UnicodeDataTest.Auxiliary.Segmentation

private def wb (c : UInt32) : WordBreak :=
  lookupWordBreak c

private def sb (c : UInt32) : SentenceBreak :=
  lookupSentenceBreak c

private def prevIndexIf (xs : Array UInt32) (i : Nat) (p : UInt32 → Bool) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    if p xs[j]! then
      return some j
  return none

private def nextIndexIf (xs : Array UInt32) (i : Nat) (p : UInt32 → Bool) : Option Nat := Id.run do
  let mut j := i
  while j < xs.size do
    if p xs[j]! then
      return some j
    j := j + 1
  return none

private def wordIgnore (c : UInt32) : Bool :=
  match wb c with
  | .extend | .format | .zwj => true
  | _ => false

private def wordSignificant (c : UInt32) : Bool :=
  !wordIgnore c

private def wordNewline (c : UInt32) : Bool :=
  match wb c with
  | .cr | .lf | .newline => true
  | _ => false

private def ahLetter (c : UInt32) : Bool :=
  match wb c with
  | .aLetter | .hebrewLetter => true
  | _ => false

private def midLetterOrMidNumLetQ (c : UInt32) : Bool :=
  match wb c with
  | .midLetter | .midNumLet | .singleQuote => true
  | _ => false

private def midNumOrMidNumLetQ (c : UInt32) : Bool :=
  match wb c with
  | .midNum | .midNumLet | .singleQuote => true
  | _ => false

private def wordExtendNumLetBase (c : UInt32) : Bool :=
  ahLetter c || wb c == .numeric || wb c == .katakana || wb c == .extendNumLet

private def prevWord? (xs : Array UInt32) (i : Nat) : Option Nat :=
  prevIndexIf xs i wordSignificant

private def nextWord? (xs : Array UInt32) (i : Nat) : Option Nat :=
  nextIndexIf xs i wordSignificant

private def prevPrevWord? (xs : Array UInt32) (i : Nat) : Option Nat :=
  match prevWord? xs i with
  | some j => prevWord? xs j
  | none => none

private def countPrevWordRI (xs : Array UInt32) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut n := 0
  while j > 0 do
    j := j - 1
    if wordIgnore xs[j]! then
      continue
    if wb xs[j]! == .regionalIndicator then
      n := n + 1
    else
      break
  return n

private def breakBetweenWordSignificant (xs : Array UInt32) (pIdx cIdx : Nat) : Bool := Id.run do
  let p := xs[pIdx]!
  let c := xs[cIdx]!
  let pW := wb p
  let cW := wb c
  if pW == .cr && cW == .lf then
    return false
  else if wordNewline p || wordNewline c then
    return true
  else if pW == .zwj && lookupExtendedPictographic c then
    return false
  else if pW == .wSegSpace && cW == .wSegSpace && pIdx + 1 == cIdx then
    return false
  else if pW == .hebrewLetter && cW == .singleQuote then
    return false
  else if pW == .hebrewLetter && cW == .doubleQuote then
    match nextWord? xs (cIdx + 1) with
    | some nIdx => return wb xs[nIdx]! != .hebrewLetter
    | none => return true
  else if pW == .doubleQuote && cW == .hebrewLetter then
    match prevPrevWord? xs cIdx with
    | some ppIdx => return wb xs[ppIdx]! != .hebrewLetter
    | none => return true
  else if ahLetter p && ahLetter c then
    return false
  else if ahLetter p && midLetterOrMidNumLetQ c then
    match nextWord? xs (cIdx + 1) with
    | some nIdx => return !ahLetter xs[nIdx]!
    | none => return true
  else if ahLetter c && midLetterOrMidNumLetQ p then
    match prevPrevWord? xs cIdx with
    | some ppIdx => return !ahLetter xs[ppIdx]!
    | none => return true
  else if pW == .numeric && cW == .numeric then
    return false
  else if ahLetter p && cW == .numeric then
    return false
  else if pW == .numeric && ahLetter c then
    return false
  else if cW == .numeric && midNumOrMidNumLetQ p then
    match prevPrevWord? xs cIdx with
    | some ppIdx => return wb xs[ppIdx]! != .numeric
    | none => return true
  else if pW == .numeric && midNumOrMidNumLetQ c then
    match nextWord? xs (cIdx + 1) with
    | some nIdx => return wb xs[nIdx]! != .numeric
    | none => return true
  else if pW == .katakana && cW == .katakana then
    return false
  else if wordExtendNumLetBase p && cW == .extendNumLet then
    return false
  else if pW == .extendNumLet && (ahLetter c || cW == .numeric || cW == .katakana) then
    return false
  else if pW == .regionalIndicator && cW == .regionalIndicator && countPrevWordRI xs cIdx % 2 == 1 then
    return false
  else
    return true

private def shouldWordBreakBefore (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let left := xs[i - 1]!
  let right := xs[i]!
  if wb left == .cr && wb right == .lf then
    return false
  else if wb left == .zwj && lookupExtendedPictographic right then
    return false
  else if wordNewline left || wordNewline right then
    return true
  else if wordIgnore right then
    return !wordIgnore left && wordNewline left
  else
    match prevWord? xs i with
    | some pIdx => return breakBetweenWordSignificant xs pIdx i
    | none => return true

/-- Segment word boundaries, including the start and end positions. -/
public def segmentWordBoundaries (xs : Array UInt32) : Array Nat := Id.run do
  if xs.isEmpty then
    return #[0]
  let mut out := #[0]
  for i in [1:xs.size] do
    if shouldWordBreakBefore xs i then
      out := out.push i
  out := out.push xs.size
  return out

private def sentenceIgnore (c : UInt32) : Bool :=
  match sb c with
  | .extend | .format => true
  | _ => false

private def sentenceSignificant (c : UInt32) : Bool :=
  !sentenceIgnore c

private def paraSep (c : UInt32) : Bool :=
  match sb c with
  | .sep | .cr | .lf => true
  | _ => false

private def satTerm (c : UInt32) : Bool :=
  match sb c with
  | .aTerm | .sTerm => true
  | _ => false

private def close (c : UInt32) : Bool :=
  sb c == .close

private def sp (c : UInt32) : Bool :=
  sb c == .sp

private def sb8Stop (c : UInt32) : Bool :=
  match sb c with
  | .oLetter | .upper | .lower => true
  | _ => paraSep c || satTerm c

private def prevSentence? (xs : Array UInt32) (i : Nat) : Option Nat :=
  prevIndexIf xs i sentenceSignificant

private def nextSentence? (xs : Array UInt32) (i : Nat) : Option Nat :=
  nextIndexIf xs i sentenceSignificant

private def prevBeforeClose (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    if sentenceIgnore xs[j]! || close xs[j]! then
      continue
    return some j
  return none

private def prevBeforeCloseSp (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  let mut skippingSp := true
  while j > 0 do
    j := j - 1
    let c := xs[j]!
    if sentenceIgnore c then
      continue
    if skippingSp && sp c then
      continue
    skippingSp := false
    if close c then
      continue
    return some j
  return none

private def nextLowerBeforeSB8Stop (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let mut j := i
  while j < xs.size do
    let c := xs[j]!
    if sentenceIgnore c then
      j := j + 1
      continue
    if sb c == .lower then
      return true
    if sb8Stop c then
      return false
    j := j + 1
  return false

private def breakBetweenSentenceSignificant (xs : Array UInt32) (pIdx cIdx : Nat) : Bool := Id.run do
  let p := xs[pIdx]!
  let c := xs[cIdx]!
  let pS := sb p
  let cS := sb c
  if pS == .cr && cS == .lf then
    return false
  else if paraSep p then
    return true
  else
    let leftClose := prevBeforeClose xs cIdx
    let leftCloseSp := prevBeforeCloseSp xs cIdx
    if pS == .aTerm && cS == .numeric then
      return false
    else if pS == .aTerm && cS == .upper then
      match prevBeforeClose xs pIdx with
      | some ppIdx =>
          let ppS := sb xs[ppIdx]!
          if ppS == .upper || ppS == .lower then
            return false
          else
            return true
      | none => return true
    else if (match leftCloseSp with | some j => sb xs[j]! == SentenceBreak.aTerm | none => false) &&
        nextLowerBeforeSB8Stop xs cIdx then
      return false
    else if match leftCloseSp with | some j => satTerm xs[j]! | none => false then
      if cS == SentenceBreak.sContinue || satTerm c then
        return false
      else if sp c || paraSep c then
        return false
      else if match leftClose with | some j => satTerm xs[j]! | none => false then
        if close c then
          return false
        else
          return true
      else
        return true
    else if match leftClose with | some j => satTerm xs[j]! | none => false then
      if close c || sp c || paraSep c then
        return false
      else
        return true
    else
      return false

private def shouldSentenceBreakBefore (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let left := xs[i - 1]!
  let right := xs[i]!
  if sb left == .cr && sb right == .lf then
    return false
  else if paraSep left then
    return true
  else if sentenceIgnore right then
    return !sentenceIgnore left && paraSep left
  else
    match prevSentence? xs i with
    | some pIdx =>
        if paraSep xs[pIdx]! then
          return false
        else
          return breakBetweenSentenceSignificant xs pIdx i
    | none => return false

/-- Segment sentence boundaries, including the start and end positions. -/
public def segmentSentenceBoundaries (xs : Array UInt32) : Array Nat := Id.run do
  if xs.isEmpty then
    return #[0]
  let mut out := #[0]
  for i in [1:xs.size] do
    if shouldSentenceBreakBefore xs i then
      out := out.push i
  out := out.push xs.size
  return out

private def runBoundaries
    (file : String)
    (cases : Array UnicodeDataTest.BreakTestCase)
    (segment : Array UInt32 → Array Nat) :
    Array UnicodeDataTest.Common.Failure := Id.run do
  let mut failures := #[]
  for tc in cases do
    let actual := segment tc.codepoints
    if actual != tc.boundaries then
      failures := failures.push {
        file := file
        line := tc.line
        expected := s!"{tc.boundaries}"
        actual := s!"{actual}"
        comment := tc.comment
      }
  return failures

public def runWordConformance (file : String) (cases : Array UnicodeDataTest.BreakTestCase) : Array UnicodeDataTest.Common.Failure :=
  runBoundaries file cases segmentWordBoundaries

public def runSentenceConformance (file : String) (cases : Array UnicodeDataTest.BreakTestCase) : Array UnicodeDataTest.Common.Failure :=
  runBoundaries file cases segmentSentenceBoundaries

end UnicodeDataTest.Auxiliary.Segmentation
