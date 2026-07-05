/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Structure containing supported character properties from `PropList.txt` -/
public structure PropList where
  /-- property `Diacritic` -/
  public diacritic : Array (UInt32 × Option UInt32) := #[]
  /-- property `Sentence_Terminal` -/
  public sentenceTerminal : Array (UInt32 × Option UInt32) := #[]
  /-- property `Pattern_Syntax` -/
  public patternSyntax : Array (UInt32 × Option UInt32) := #[]
  /-- property `Pattern_White_Space` -/
  public patternWhiteSpace : Array (UInt32 × Option UInt32) := #[]

  /-- property `Extender` -/
  public extender : Array (UInt32 × Option UInt32) := #[]
  /-- property `Regional_Indicator` -/
  public regionalIndicator : Array (UInt32 × Option UInt32) := #[]

  /-- property `Dash` -/
  public dash : Array (UInt32 × Option UInt32) := #[]
  /-- property `Hyphen` -/
  public hyphen : Array (UInt32 × Option UInt32) := #[]
  /-- property `Quotation_Mark` -/
  public quotationMark : Array (UInt32 × Option UInt32) := #[]
  /-- property `Terminal_Punctuation` -/
  public terminalPunctuation : Array (UInt32 × Option UInt32) := #[]

  /-- property `Noncharacter_Code_Point` -/
  public noncharacterCodePoint : Array (UInt32 × Option UInt32) := #[]
  /-- property `White_Space` -/
  public whiteSpace : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Math` -/
  public otherMath : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Alphabetic` -/
  public otherAlphabetic : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Lowercase` -/
  public otherLowercase : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Uppercase` -/
  public otherUppercase : Array (UInt32 × Option UInt32) := #[]
  /-- property `Other_Default_Ignorable_Code_Point` -/
  public otherDefaultIgnorableCodePoint : Array (UInt32 × Option UInt32) := #[]
  /-- property `Prepended_Concatenation_Mark` -/
  public prependedConcatenationMark : Array (UInt32 × Option UInt32) := #[]
  /-- property `Variation_Selector` -/
  public variationSelector : Array (UInt32 × Option UInt32) := #[]
  /-- property `Deprecated` -/
  deprecated : Array (UInt32 × Option UInt32) := #[]
deriving Inhabited, Repr

/-- Raw string form `PropList.txt` -/
protected def PropList.txt := include_str "../../data-ucd/core/PropList.txt"

public unsafe initialize PropList.data : PropList ←
  let stream := UCDStream.ofString PropList.txt
  let mut list : PropList := {}
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in PropList.txt"
    if record[1]! == "Noncharacter_Code_Point" then
      list := {list with noncharacterCodePoint := list.noncharacterCodePoint.push val}
    if record[1]! == "White_Space" then
      list := {list with whiteSpace := list.whiteSpace.push val}
    if record[1]! == "Other_Math" then
      list := {list with otherMath := list.otherMath.push val}
    if record[1]! == "Other_Alphabetic" then
      list := {list with otherAlphabetic := list.otherAlphabetic.push val}
    if record[1]! == "Other_Lowercase" then
      list := {list with otherLowercase := list.otherLowercase.push val}
    if record[1]! == "Other_Uppercase" then
      list := {list with otherUppercase := list.otherUppercase.push val}
    if record[1]! == "Other_Default_Ignorable_Code_Point" then
      list := {list with otherDefaultIgnorableCodePoint := list.otherDefaultIgnorableCodePoint.push val}
    if record[1]! == "Prepended_Concatenation_Mark" then
      list := {list with prependedConcatenationMark := list.prependedConcatenationMark.push val}
    if record[1]! == "Variation_Selector" then
      list := {list with variationSelector := list.variationSelector.push val}

    if record[1]! == "Dash" then
      list := {list with dash := list.dash.push val}
    if record[1]! == "Hyphen" then
      list := {list with hyphen := list.hyphen.push val}
    if record[1]! == "Quotation_Mark" then
      list := {list with quotationMark := list.quotationMark.push val}
    if record[1]! == "Terminal_Punctuation" then
      list := {list with terminalPunctuation := list.terminalPunctuation.push val}

    if record[1]! == "Extender" then
      list := {list with extender := list.extender.push val}
    if record[1]! == "Regional_Indicator" then
      list := {list with regionalIndicator := list.regionalIndicator.push val}

    if record[1]! == "Diacritic" then
      list := {list with diacritic := list.diacritic.push val}
    if record[1]! == "Sentence_Terminal" then
      list := {list with sentenceTerminal := list.sentenceTerminal.push val}
    if record[1]! == "Pattern_Syntax" then
      list := {list with patternSyntax := list.patternSyntax.push val}
    if record[1]! == "Pattern_White_Space" then
      list := {list with patternWhiteSpace := list.patternWhiteSpace.push val}
    if record[1]! == "Deprecated" then
      list := {list with deprecated := list.deprecated.push val}
  return list

-- TODO: stop reinventing the wheel!
/-- Binary search -/
private partial def find (code : UInt32) (data : Array (UInt32 × Option UInt32)) (lo hi : Nat) : Nat :=
  assert! (hi ≤ data.size)
  assert! (lo < hi)
  assert! (data[lo]!.fst ≤ code)
  let mid := (lo + hi) / 2 -- NB: mid < hi because lo < hi
  if lo = mid then
    mid
  else
    if code < data[mid]!.fst then
      find code data lo mid
    else
      find code data mid hi

/-- Check if code point has `Noncharacter_Code_Point` property from `PropList.txt` -/
@[inline]
public def PropList.isNoncharacterCodePoint (code : UInt32) : Bool :=
  let data := PropList.data.noncharacterCodePoint
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `White_Space` property from `PropList.txt` -/
@[inline]
public def PropList.isWhiteSpace (code : UInt32) : Bool :=
  let data := PropList.data.whiteSpace
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Math` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherMath (code : UInt32) : Bool :=
  let data := PropList.data.otherMath
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Alphabetic` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherAlphabetic (code : UInt32) : Bool :=
  let data := PropList.data.otherAlphabetic
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Lowercase` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherLowercase (code : UInt32) : Bool :=
  let data := PropList.data.otherLowercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Uppercase` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherUppercase (code : UInt32) : Bool :=
  let data := PropList.data.otherUppercase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Other_Default_Ignorable_Code_Point` property from `PropList.txt` -/
@[inline]
public def PropList.isOtherDefaultIgnorableCodePoint (code : UInt32) : Bool :=
  let data := PropList.data.otherDefaultIgnorableCodePoint
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Prepended_Concatenation_Mark` property from `PropList.txt` -/
@[inline]
public def PropList.isPrependedConcatenationMark (code : UInt32) : Bool :=
  let data := PropList.data.prependedConcatenationMark
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Variation_Selector` property from `PropList.txt` -/
@[inline]
public def PropList.isVariationSelector (code : UInt32) : Bool :=
  let data := PropList.data.variationSelector
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Deprecated` property from `PropList.txt` -/
@[inline]
public def PropList.isDeprecated (code : UInt32) : Bool :=
  let data := PropList.data.deprecated
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Dash` property from `PropList.txt` -/
@[inline]
public def PropList.isDash (code : UInt32) : Bool :=
  let data := PropList.data.dash
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Hyphen` property from `PropList.txt` -/
@[inline]
public def PropList.isHyphen (code : UInt32) : Bool :=
  let data := PropList.data.hyphen
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Quotation_Mark` property from `PropList.txt` -/
@[inline]
public def PropList.isQuotationMark (code : UInt32) : Bool :=
  let data := PropList.data.quotationMark
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Terminal_Punctuation` property from `PropList.txt` -/
@[inline]
public def PropList.isTerminalPunctuation (code : UInt32) : Bool :=
  let data := PropList.data.terminalPunctuation
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Extender` property from `PropList.txt` -/
@[inline]
public def PropList.isExtender (code : UInt32) : Bool :=
  let data := PropList.data.extender
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Regional_Indicator` property from `PropList.txt` -/
@[inline]
public def PropList.isRegionalIndicator (code : UInt32) : Bool :=
  let data := PropList.data.regionalIndicator
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Diacritic` property -/
@[inline]
public def PropList.isDiacritic (code : UInt32) : Bool :=
  let data := PropList.data.diacritic
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Sentence_Terminal` property -/
@[inline]
public def PropList.isSentenceTerminal (code : UInt32) : Bool :=
  let data := PropList.data.sentenceTerminal
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Pattern_Syntax` property -/
@[inline]
public def PropList.isPatternSyntax (code : UInt32) : Bool :=
  let data := PropList.data.patternSyntax
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

/-- Check if code point has `Pattern_White_Space` property -/
@[inline]
public def PropList.isPatternWhiteSpace (code : UInt32) : Bool :=
  let data := PropList.data.patternWhiteSpace
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top
