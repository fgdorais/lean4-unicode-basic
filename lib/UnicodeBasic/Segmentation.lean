/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic.TableLookup.WordBreak
import UnicodeBasic.TableLookup.SentenceBreak
import UnicodeBasic.TableLookup.ExtendedPictographic
import UnicodeBasic.TableLookup.LineBreak
import UnicodeBasic.TableLookup.GeneralCategory
import UnicodeBasic.TableLookup.EastAsianWidth

namespace Unicode

private def wb (c : UInt32) : MaybeWordBreak :=
  lookupWordBreak c

private def sb (c : UInt32) : MaybeSentenceBreak :=
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
  while h : j < xs.size do
    if p xs[j] then
      return some j
    j := j + 1
  return none

private def wordIgnore (c : UInt32) : Bool :=
  match wb c with
  | .nonOther .extend | .nonOther .format | .nonOther .zwj => true
  | _ => false

private def wordSignificant (c : UInt32) : Bool :=
  !wordIgnore c

private def wordNewline (c : UInt32) : Bool :=
  match wb c with
  | .nonOther .cr | .nonOther .lf | .nonOther .newline => true
  | _ => false

private def ahLetter (c : UInt32) : Bool :=
  match wb c with
  | .nonOther .aLetter | .nonOther .hebrewLetter => true
  | _ => false

private def midLetterOrMidNumLetQ (c : UInt32) : Bool :=
  match wb c with
  | .nonOther .midLetter | .nonOther .midNumLet | .nonOther .singleQuote => true
  | _ => false

private def midNumOrMidNumLetQ (c : UInt32) : Bool :=
  match wb c with
  | .nonOther .midNum | .nonOther .midNumLet | .nonOther .singleQuote => true
  | _ => false

private def wordExtendNumLetBase (c : UInt32) : Bool :=
  ahLetter c || wb c == .nonOther .numeric || wb c == .nonOther .katakana || wb c == .nonOther .extendNumLet

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
    let c := xs[j]!
    if wordIgnore c then
      continue
    if wb c == .nonOther .regionalIndicator then
      n := n + 1
    else
      break
  return n

private def breakBetweenWordSignificant (xs : Array UInt32) (pIdx cIdx : Nat) : Bool := Id.run do
  let p := xs[pIdx]!
  let c := xs[cIdx]!
  let pW := wb p
  let cW := wb c
  if pW == .nonOther .cr && cW == .nonOther .lf then
    return false
  else if wordNewline p || wordNewline c then
    return true
  else if pW == .nonOther .zwj && lookupExtendedPictographic c then
    return false
  else if pW == .nonOther .wSegSpace && cW == .nonOther .wSegSpace && pIdx + 1 == cIdx then
    return false
  else if pW == .nonOther .hebrewLetter && cW == .nonOther .singleQuote then
    return false
  else if pW == .nonOther .hebrewLetter && cW == .nonOther .doubleQuote then
    match nextWord? xs (cIdx + 1) with
    | some nIdx => return wb xs[nIdx]! != .nonOther .hebrewLetter
    | none => return true
  else if pW == .nonOther .doubleQuote && cW == .nonOther .hebrewLetter then
    match prevPrevWord? xs cIdx with
    | some ppIdx => return wb xs[ppIdx]! != .nonOther .hebrewLetter
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
  else if pW == .nonOther .numeric && cW == .nonOther .numeric then
    return false
  else if ahLetter p && cW == .nonOther .numeric then
    return false
  else if pW == .nonOther .numeric && ahLetter c then
    return false
  else if cW == .nonOther .numeric && midNumOrMidNumLetQ p then
    match prevPrevWord? xs cIdx with
    | some ppIdx => return wb xs[ppIdx]! != .nonOther .numeric
    | none => return true
  else if pW == .nonOther .numeric && midNumOrMidNumLetQ c then
    match nextWord? xs (cIdx + 1) with
    | some nIdx => return wb xs[nIdx]! != .nonOther .numeric
    | none => return true
  else if pW == .nonOther .katakana && cW == .nonOther .katakana then
    return false
  else if wordExtendNumLetBase p && cW == .nonOther .extendNumLet then
    return false
  else if pW == .nonOther .extendNumLet && (ahLetter c || cW == .nonOther .numeric || cW == .nonOther .katakana) then
    return false
  else if pW == .nonOther .regionalIndicator && cW == .nonOther .regionalIndicator && countPrevWordRI xs cIdx % 2 == 1 then
    return false
  else
    return true

private def shouldWordBreakBefore (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let left := xs[i - 1]!
  let right := xs[i]!
  if wb left == .nonOther .cr && wb right == .nonOther .lf then
    return false
  else if wb left == .nonOther .zwj && lookupExtendedPictographic right then
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
  | .nonOther .extend | .nonOther .format => true
  | _ => false

private def sentenceSignificant (c : UInt32) : Bool :=
  !sentenceIgnore c

private def paraSep (c : UInt32) : Bool :=
  match sb c with
  | .nonOther .sep | .nonOther .cr | .nonOther .lf => true
  | _ => false

private def satTerm (c : UInt32) : Bool :=
  match sb c with
  | .nonOther .aTerm | .nonOther .sTerm => true
  | _ => false

private def close (c : UInt32) : Bool :=
  sb c == .nonOther .close

private def sp (c : UInt32) : Bool :=
  sb c == .nonOther .sp

private def sb8Stop (c : UInt32) : Bool :=
  match sb c with
  | .nonOther .oLetter | .nonOther .upper | .nonOther .lower => true
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
    if sb c == .nonOther .lower then
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
  if pS == .nonOther .cr && cS == .nonOther .lf then
    return false
  else if paraSep p then
    return true
  else
    let leftClose := prevBeforeClose xs cIdx
    let leftCloseSp := prevBeforeCloseSp xs cIdx
    if pS == .nonOther .aTerm && cS == .nonOther .numeric then
      return false
    else if pS == .nonOther .aTerm && cS == .nonOther .upper then
      match prevBeforeClose xs pIdx with
      | some ppIdx =>
          let ppS := sb xs[ppIdx]!
          if ppS == .nonOther .upper || ppS == .nonOther .lower then
            return false
          else
            return true
      | none => return true
    else if (match leftCloseSp with | some j => sb xs[j]! == .nonOther .aTerm | none => false) &&
        nextLowerBeforeSB8Stop xs cIdx then
      return false
    else if match leftCloseSp with | some j => satTerm xs[j]! | none => false then
      if cS == .nonOther .sContinue || satTerm c then
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
  if sb left == .nonOther .cr && sb right == .nonOther .lf then
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

private def resolveLineBreakRaw (c : UInt32) : LineBreak :=
  match lookupLineBreak c with
  | .complexContext =>
      let gc := lookupGC c
      if GC.Mn ⊆ gc || GC.Mc ⊆ gc then
        .combiningMark
      else
        .alphabetic
  | .ambiguous | .unknown | .surrogate => .alphabetic
  | .conditionalJapaneseStarter => .nonstarter
  | other => other

private partial def lineBreakClassAt (xs : Array UInt32) (i : Nat) : LineBreak := Id.run do
  let lb := resolveLineBreakRaw xs[i]!
  match lb with
  | .combiningMark | .zwj =>
      if i = 0 then
        return .alphabetic
      let mut j := i
      while j > 0 do
        j := j - 1
        let p := resolveLineBreakRaw xs[j]!
        match p with
        | .combiningMark | .zwj => continue
        | .space | .mandatoryBreak | .carriageReturn | .lineFeed | .nextLine | .zwSpace =>
            return .alphabetic
        | _ => return lineBreakClassAt xs j
      return .alphabetic
  | _ => return lb

private def isLineSpace (lb : LineBreak) : Bool :=
  lb == .space

private def isLineHardBreak (lb : LineBreak) : Bool :=
  match lb with
  | .mandatoryBreak | .carriageReturn | .lineFeed | .nextLine => true
  | _ => false

private def isEastAsian (c : UInt32) : Bool :=
  match lookupEastAsianWidth c with
  | EastAsianWidth.fullwidth | EastAsianWidth.halfwidth | EastAsianWidth.wide => true
  | _ => false

private def isInitialPunctuation (c : UInt32) : Bool :=
  GC.Pi ⊆ lookupGC c

private def isFinalPunctuation (c : UInt32) : Bool :=
  GC.Pf ⊆ lookupGC c

private def isUnassigned (c : UInt32) : Bool :=
  GC.Cn ⊆ lookupGC c

private def prevNonSpace? (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    if !isLineSpace (lineBreakClassAt xs j) then
      return some j
  return none

private def nextNonSpace? (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j < xs.size do
    if !isLineSpace (lineBreakClassAt xs j) then
      return some j
    j := j + 1
  return none

private def inOpenAfter (lb : LineBreak) : Bool :=
  lb == .openPunctuation || lb == .quotation || lb == .breakBefore

private def inCloseBefore (lb : LineBreak) : Bool :=
  lb == .closePunctuation || lb == .closeParenthesis || lb == .exclamation || lb == .breakSymbols

private def inNumericish (lb : LineBreak) : Bool :=
  lb == .numeric || lb == .prefixNumeric || lb == .postfixNumeric || lb == .infixNumeric

private def isALHL (lb : LineBreak) : Bool :=
  lb == .alphabetic || lb == .hebrewLetter

private def inAlphaish (lb : LineBreak) : Bool :=
  lb == .alphabetic || lb == .hebrewLetter || lb == .ideographic || lb == .aksara ||
    lb == .aksaraPrebase || lb == .aksaraStart || lb == .h2 || lb == .h3 || lb == .jl ||
    lb == .jt || lb == .jv || lb == .nonstarter

private def isHangul (lb : LineBreak) : Bool :=
  lb == .jl || lb == .jv || lb == .jt || lb == .h2 || lb == .h3

private def isIDEBEM (lb : LineBreak) : Bool :=
  lb == .ideographic || lb == .eBase || lb == .eModifier

private def isAKLike (lb : LineBreak) : Bool :=
  lb == .aksara || lb == .aksaraStart

private def isBrahmicBase (lb : LineBreak) (c : UInt32) : Bool :=
  isAKLike lb || c == 0x25CC

private def isBrahmicBaseOrAS (lb : LineBreak) (c : UInt32) : Bool :=
  isBrahmicBase lb c || lb == .aksaraStart

private def isHebrewHyphenContext (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  if i = 0 then
    return false
  let lb := lineBreakClassAt xs i
  if lb != .hyphen && lb != .unambiguousHyphen then
    return false
  match prevNonSpace? xs i with
  | some pIdx =>
      if lineBreakClassAt xs pIdx != .hebrewLetter then
        return false
      match nextNonSpace? xs (i + 1) with
      | some nIdx => return lineBreakClassAt xs nIdx != .hebrewLetter
      | none => return true
  | none => false

private def isWordInitialHyphen (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let lb := lineBreakClassAt xs i
  if lb != .hyphen && lb != .unambiguousHyphen then
    return false
  if i = 0 then
    return true
  if lineBreakClassAt xs (i - 1) == .space then
    return true
  match prevNonSpace? xs i with
  | some pIdx =>
    let p := lineBreakClassAt xs pIdx
    return isLineHardBreak p || p == .space || p == .zwSpace || p == .contingentBreak ||
      p == .glue || p == .openPunctuation
  | none => true

private def hasOnlySpacesAfter (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let mut j := i + 1
  while j < xs.size do
    if !isLineSpace (lineBreakClassAt xs j) then
      return false
    j := j + 1
  return true

private def countPrevLineRI (xs : Array UInt32) (i : Nat) : Nat := Id.run do
  let mut n := 0
  let mut j := i
  while j > 0 do
    j := j - 1
    let raw := resolveLineBreakRaw xs[j]!
    if raw == .combiningMark || raw == .zwj then
      continue
    let lb := lineBreakClassAt xs j
    if isLineSpace lb then
      continue
    if lb == .regionalIndicator then
      n := n + 1
    else
      break
  return n

private def hasNumericBeforeSeparators (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    let lb := lineBreakClassAt xs j
    if lb == .infixNumeric || lb == .breakSymbols then
      continue
    return lb == .numeric
  return false

private def prevClass? (xs : Array UInt32) (i : Nat) : Option LineBreak :=
  prevNonSpace? xs i |>.map fun j => lineBreakClassAt xs j

private def nextClass? (xs : Array UInt32) (i : Nat) : Option LineBreak :=
  nextNonSpace? xs i |>.map fun j => lineBreakClassAt xs j

private def isInitialQuoteContext (xs : Array UInt32) (qIdx : Nat) : Bool :=
  lineBreakClassAt xs qIdx == .quotation && isInitialPunctuation xs[qIdx]! &&
    (qIdx == 0 || lineBreakClassAt xs (qIdx - 1) == .space ||
    match prevNonSpace? xs qIdx with
    | none => true
    | some pIdx =>
        let p := lineBreakClassAt xs pIdx
        isLineHardBreak p || p == .openPunctuation || p == .quotation || p == .glue || p == .zwSpace)

private def isInitialQuoteEastAsianSurrounded (xs : Array UInt32) (qIdx : Nat) : Bool :=
  isInitialPunctuation xs[qIdx]! &&
    (qIdx > 0 && isEastAsian xs[qIdx - 1]!) &&
    match nextNonSpace? xs (qIdx + 1) with
    | some nIdx => isEastAsian xs[nIdx]!
    | none => false

private def isFinalQuoteEastAsianSurrounded (xs : Array UInt32) (qIdx : Nat) : Bool :=
  isFinalPunctuation xs[qIdx]! &&
    (match prevNonSpace? xs qIdx with
    | some pIdx => isEastAsian xs[pIdx]!
    | none => false) &&
    (qIdx + 1 < xs.size && isEastAsian xs[qIdx + 1]!)

private def prevLineBaseIndex? (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    match resolveLineBreakRaw xs[j]! with
    | .combiningMark | .zwj => continue
    | _ => return some j
  return none

private def prevNonSpaceBaseIndex? (xs : Array UInt32) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    let lb := lineBreakClassAt xs j
    let raw := resolveLineBreakRaw xs[j]!
    if lb == .space || raw == .combiningMark || raw == .zwj then
      continue
    return some j
  return none

private def breakBeforeLine (xs : Array UInt32) (i : Nat) : Bool := Id.run do
  if i = 0 then
    return false
  let left := lineBreakClassAt xs (i - 1)
  let right := lineBreakClassAt xs i
  let rawLeft := resolveLineBreakRaw xs[i - 1]!
  let rawRight := resolveLineBreakRaw xs[i]!
  let leftCtxIdx? := prevNonSpaceBaseIndex? xs i
  let leftCtx? := prevClass? xs i
  let rightNext? := nextClass? xs (i + 1)
  let leftCtx := leftCtx?.getD left
  let leftBaseIdx := (prevLineBaseIndex? xs i).getD (i - 1)
  let leftBase := lineBreakClassAt xs leftBaseIdx
  let leftBaseChar := xs[leftBaseIdx]!
  let beforeLeftBaseIdx := (prevLineBaseIndex? xs (i - 1)).getD (i - 1)
  let beforeLeftBase := lineBreakClassAt xs beforeLeftBaseIdx
  let beforeLeftBaseChar := xs[beforeLeftBaseIdx]!
  if left == .carriageReturn && right == .lineFeed then
    return false
  else if isLineHardBreak left then
    return true
  else if isLineHardBreak right then
    return false
  else if right == .space || right == .zwSpace then
    return false
  else if left == .zwSpace then
    return true
  else if leftCtx == .zwSpace then
    return true
  else if rawLeft == .zwj then
    return false
  else if (rawRight == .combiningMark || rawRight == .zwj) && left != .space then
    return false
  else if right == .zwj then
    return false
  else if left == .wordJoiner || right == .wordJoiner then
    return false
  else if left == .glue then
    return false
  else if right == .glue && left != .space && left != .breakAfter && left != .hyphen && left != .unambiguousHyphen then
    return false
  else if inCloseBefore right then
    return false
  else if leftCtx == .openPunctuation then
    return false
  else if left == .quotation && isInitialPunctuation xs[i - 1]! then
    return false
  else if (leftCtx == .closePunctuation || leftCtx == .closeParenthesis) && right == .nonstarter then
    return false
  else if leftCtx == .breakBoth && right == .breakBoth then
    return false
  else if left == .space && right == .infixNumeric && (match rightNext? with | some .numeric => true | _ => false) then
    return true
  else if right == .infixNumeric then
    return false
  else if (match leftCtxIdx? with | some qIdx => isInitialQuoteContext xs qIdx | none => false) then
    return false
  else if right == .quotation && isFinalPunctuation xs[i]! &&
      (if i + 1 >= xs.size then
        true
      else
        let n := lineBreakClassAt xs (i + 1)
        n == .space || n == .glue || n == .wordJoiner || n == .closePunctuation ||
          n == .quotation || n == .closeParenthesis || n == .exclamation ||
          n == .infixNumeric || n == .breakSymbols || isLineHardBreak n || n == .zwSpace) then
    return false
  else if left == .space then
    return true
  else if left == .quotation && !isFinalQuoteEastAsianSurrounded xs (i - 1) then
    return false
  else if right == .quotation && !isInitialQuoteEastAsianSurrounded xs i then
    return false
  else if left == .contingentBreak || right == .contingentBreak then
    return true
  else if isWordInitialHyphen xs (i - 1) && isALHL right then
    return false
  else if (rawLeft == .combiningMark || rawLeft == .zwj) && isWordInitialHyphen xs leftBaseIdx && isALHL right then
    return false
  else if right == .breakAfter || right == .hyphen || right == .unambiguousHyphen || right == .nonstarter then
    return false
  else if left == .breakBefore then
    return false
  else if isHebrewHyphenContext xs (i - 1) then
    return false
  else if left == .breakSymbols && right == .hebrewLetter then
    return false
  else if right == .inseparable then
    return false
  else if isALHL left && right == .numeric then
    return false
  else if left == .numeric && isALHL right then
    return false
  else if left == .prefixNumeric && isIDEBEM right then
    return false
  else if isIDEBEM left && right == .postfixNumeric then
    return false
  else if (left == .prefixNumeric || left == .postfixNumeric) && isALHL right then
    return false
  else if isALHL left && (right == .prefixNumeric || right == .postfixNumeric) then
    return false
  else if left == .hyphen && right == .numeric then
    return false
  else if left == .infixNumeric && right == .numeric then
    return false
  else if left == .numeric && (right == .numeric || right == .breakSymbols || right == .infixNumeric || right == .postfixNumeric || right == .prefixNumeric) then
    return false
  else if (right == .postfixNumeric || right == .prefixNumeric) && hasNumericBeforeSeparators xs i then
    return false
  else if left == .breakSymbols && right == .numeric &&
      (match prevClass? xs (i - 1) with | some .numeric => true | _ => false) then
    return false
  else if (left == .postfixNumeric || left == .prefixNumeric) && right == .openPunctuation &&
      (match rightNext? with | some .numeric | some .infixNumeric => true | _ => false) then
    return false
  else if (left == .postfixNumeric || left == .prefixNumeric) &&
      (right == .numeric || right == .infixNumeric) then
    return false
  else if (left == .prefixNumeric || left == .postfixNumeric) && right == .hyphen then
    return false
  else if left == .numeric && (right == .closePunctuation || right == .closeParenthesis) &&
      (match rightNext? with | some .postfixNumeric | some .prefixNumeric => true | _ => false) then
    return false
  else if (left == .closePunctuation || left == .closeParenthesis) &&
      (right == .postfixNumeric || right == .prefixNumeric) &&
      (match prevClass? xs (i - 1) with | some .numeric => true | _ => false) then
    return false
  else if left == .jl && (right == .jl || right == .jv || right == .h2 || right == .h3) then
    return false
  else if (left == .jv || left == .h2) && (right == .jv || right == .jt) then
    return false
  else if (left == .jt || left == .h3) && right == .jt then
    return false
  else if isHangul left && right == .postfixNumeric then
    return false
  else if left == .prefixNumeric && isHangul right then
    return false
  else if isALHL left && isALHL right then
    return false
  else if left == .aksaraPrebase && isBrahmicBaseOrAS right xs[i]! then
    return false
  else if isBrahmicBaseOrAS leftBase leftBaseChar && (right == .viramaFinal || right == .virama) then
    return false
  else if left == .virama && isBrahmicBase right xs[i]! &&
      isBrahmicBaseOrAS beforeLeftBase beforeLeftBaseChar then
    return false
  else if (rawLeft == .combiningMark || rawLeft == .zwj) && leftBase == .virama &&
      isBrahmicBase right xs[i]! &&
      (let beforeViramaIdx := (prevLineBaseIndex? xs leftBaseIdx).getD leftBaseIdx
       isBrahmicBaseOrAS (lineBreakClassAt xs beforeViramaIdx) xs[beforeViramaIdx]!) then
    return false
  else if isBrahmicBaseOrAS leftBase leftBaseChar && isBrahmicBaseOrAS right xs[i]! &&
      (match rightNext? with | some .viramaFinal => true | _ => false) then
    return false
  else if left == .infixNumeric && isALHL right then
    return false
  else if (isALHL left || left == .numeric) && right == .openPunctuation && !isEastAsian xs[i]! then
    return false
  else if left == .closeParenthesis && !isEastAsian xs[i - 1]! && (isALHL right || right == .numeric) then
    return false
  else if left == .regionalIndicator && right == .regionalIndicator then
    return countPrevLineRI xs i % 2 == 0
  else if (leftBase == .eBase || (lookupExtendedPictographic leftBaseChar && isUnassigned leftBaseChar)) && right == .eModifier then
    return false
  else if left == .breakAfter then
    return true
  else
    true

/-- Segment line break opportunities, including the terminal position. -/
public def segmentLineBoundaries (xs : Array UInt32) : Array Nat := Id.run do
  if xs.isEmpty then
    return #[]
  let mut out := #[]
  for i in [1:xs.size] do
    if breakBeforeLine xs i then
      out := out.push i
  out := out.push xs.size
  return out

end Unicode
