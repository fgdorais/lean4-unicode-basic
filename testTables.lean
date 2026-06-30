/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
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

def testDefautlIgnorableCodePoint (d : UnicodeData) : Bool :=
  let v :=
    d.gc == .Cf
      || PropList.isOtherDefaultIgnorableCodePoint d.code
        || PropList.isVariationSelector d.code
  let v := v
    && !(0xFFF9 ≤ d.code && d.code ≤ 0xFFFB)
      && !(0x13430 ≤ d.code && d.code ≤ 0x1343F)
        && !PropList.isWhiteSpace d.code
          && !PropList.isPrependedConcatenationMark d.code
  v == lookupDefaultIgnorableCodePoint d.code

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

def testBlockName : Bool :=
  getBlockName 'A' == "Basic Latin"
    && getBlockName '(' == "Basic Latin"

def testEastAsianWidth : Bool :=
  getEastAsianWidth 'A' == EastAsianWidth.narrow
    && getEastAsianWidth '中' == EastAsianWidth.wide

def testBidiPairedBracket : Bool :=
  getBidiPairedBracket? '(' == some (')'.val)
    && getBidiPairedBracketType? '(' == some BidiBracketType.openBracket
    && getBidiPairedBracket? ')' == some ('('.val)
    && getBidiPairedBracketType? ')' == some BidiBracketType.closeBracket

def testNoncharacterCodePoint (d : UnicodeData) : Bool :=
  PropList.isNoncharacterCodePoint d.code == lookupNoncharacterCodePoint d.code

def testDash (d : UnicodeData) : Bool :=
  PropList.isDash d.code == lookupDash d.code

def testHyphen (d : UnicodeData) : Bool :=
  PropList.isHyphen d.code == lookupHyphen d.code

def testQuotationMark (d : UnicodeData) : Bool :=
  PropList.isQuotationMark d.code == lookupQuotationMark d.code

def testTerminalPunctuation (d : UnicodeData) : Bool :=
  PropList.isTerminalPunctuation d.code == lookupTerminalPunctuation d.code

def testExtender (d : UnicodeData) : Bool :=
  PropList.isExtender d.code == lookupExtender d.code

def testRegionalIndicator (d : UnicodeData) : Bool :=
  PropList.isRegionalIndicator d.code == lookupRegionalIndicator d.code

def testIDStart (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isIDStart d.code == lookupIDStart d.code

def testIDContinue (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isIDContinue d.code == lookupIDContinue d.code

def testXIDStart (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isXIDStart d.code == lookupXIDStart d.code

def testXIDContinue (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isXIDContinue d.code == lookupXIDContinue d.code

def testDiacritic (d : UnicodeData) : Bool :=
  PropList.isDiacritic d.code == lookupDiacritic d.code

def testSentenceTerminal (d : UnicodeData) : Bool :=
  PropList.isSentenceTerminal d.code == lookupSentenceTerminal d.code

def testPatternSyntax (d : UnicodeData) : Bool :=
  PropList.isPatternSyntax d.code == lookupPatternSyntax d.code

def testPatternWhiteSpace (d : UnicodeData) : Bool :=
  PropList.isPatternWhiteSpace d.code == lookupPatternWhiteSpace d.code

def testEmoji (d : UnicodeData) : Bool :=
  EmojiData.isEmoji d.code == lookupEmoji d.code

def testEmojiPresentation (d : UnicodeData) : Bool :=
  EmojiData.isEmojiPresentation d.code == lookupEmojiPresentation d.code

def testEmojiModifier (d : UnicodeData) : Bool :=
  EmojiData.isEmojiModifier d.code == lookupEmojiModifier d.code

def testEmojiModifierBase (d : UnicodeData) : Bool :=
  EmojiData.isEmojiModifierBase d.code == lookupEmojiModifierBase d.code

def testEmojiComponent (d : UnicodeData) : Bool :=
  EmojiData.isEmojiComponent d.code == lookupEmojiComponent d.code

def testExtendedPictographic (d : UnicodeData) : Bool :=
  EmojiData.isExtendedPictographic d.code == lookupExtendedPictographic d.code

def testGraphemeBase (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isGraphemeBase d.code == lookupGraphemeBase d.code

def testGraphemeExtend (d : UnicodeData) : Bool :=
  DerivedCoreProperties.isGraphemeExtend d.code == lookupGraphemeExtend d.code

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

def tests : List (String × (UnicodeData → Bool)) := [
  ("Bidi_Class", testBidiClass),
  ("Block", fun _ => testBlockName),
  ("East_Asian_Width", fun _ => testEastAsianWidth),
  ("Alphabetic", testAlphabetic),
  ("Bidi_Class", testBidiClass),
  ("Bidi_Paired_Bracket", fun _ => testBidiPairedBracket),
  ("Bidi_Mirrored", testBidiMirrored),
  ("Canonical_Combining_Class", testCanonicalCombiningClass),
  ("Canonical_Decomposition_Mapping", testCanonicalDecompositionMapping),
  ("Case_Mapping", testCaseMapping),
  ("Cased", testCased),
  ("Decomposition_Mapping", testDecompositionMapping),
  ("Default_Ignorable_Code_Point", testDefautlIgnorableCodePoint),
  ("Dash", testDash),
  ("Diacritic", testDiacritic),
  ("Emoji", testEmoji),
  ("Emoji_Component", testEmojiComponent),
  ("Emoji_Modifier", testEmojiModifier),
  ("Emoji_Modifier_Base", testEmojiModifierBase),
  ("Emoji_Presentation", testEmojiPresentation),
  ("Extended_Pictographic", testExtendedPictographic),
  ("Extender", testExtender),
  ("Grapheme_Base", testGraphemeBase),
  ("Grapheme_Extend", testGraphemeExtend),
  ("Hyphen", testHyphen),
  ("ID_Continue", testIDContinue),
  ("ID_Start", testIDStart),
  ("Lowercase", testLowercase),
  ("Math", testMath),
  ("Name", testName),
  ("Noncharacter_Code_Point", testNoncharacterCodePoint),
  ("Pattern_Syntax", testPatternSyntax),
  ("Pattern_White_Space", testPatternWhiteSpace),
  ("Quotation_Mark", testQuotationMark),
  ("Regional_Indicator", testRegionalIndicator),
  ("Sentence_Terminal", testSentenceTerminal),
  ("Terminal_Punctuation", testTerminalPunctuation),
  ("Titlecase", testTitlecase),
  ("Uppercase", testUppercase),
  ("XID_Continue", testXIDContinue),
  ("XID_Start", testXIDStart),
  ("Numeric_Value", testNumericValue),
  ("General_Category", testGeneralCategory),
  ("White_Space", testWhiteSpace)]

public def main (args : List String) : IO UInt32 := do
  let args := if args.isEmpty then tests.map Prod.fst else args
  let stream : UnicodeDataStream := {}
  let mut err : UInt32 := 0
  for d in stream do
    for t in tests do
      if t.1 ∈ args && !t.2 d then
        err := 1
        IO.println s!"Error: {t.1} {toHexStringRaw d.code}"
  return err
