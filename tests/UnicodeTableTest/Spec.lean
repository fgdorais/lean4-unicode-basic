/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Spec.Tree
import UnicodeBasic
import UnicodeData
import Std.Time.Time.Unit.Basic
import Std.Time.Time.Unit.Second

open Unicode

namespace UnicodeTableTest

def lookupRange? (code : UInt32) (data : Array (UInt32 × UInt32 × α)) : Option α :=
  data.findSome? fun (c₀, c₁, v) =>
    if c₀ ≤ code && code ≤ c₁ then some v else none

def lookupRangeOpt? (code : UInt32) (data : Array (UInt32 × Option UInt32 × α)) : Option α :=
  data.findSome? fun (c₀, c₁?, v) =>
    let c₁ := c₁?.getD c₀
    if c₀ ≤ code && code ≤ c₁ then some v else none

def inRange (code : UInt32) (range : UInt32 × Option UInt32) : Bool :=
  range.1 ≤ code && code ≤ range.2.getD range.1

def inClosedRange (code : UInt32) (range : UInt32 × UInt32) : Bool :=
  range.1 ≤ code && code ≤ range.2

def testAlphabetic (d : UnicodeData) : Bool :=
  let v :=
    if d.gc ∈ [.Lu, .Ll, .Lt, .Lm, .Lo, .Nl] then true
    else PropList.isOtherAlphabetic d.code
  v == lookupAlphabetic d.code

def testBidiClass (d : UnicodeData) : Bool :=
  lookupDerivedBidiClass d.code == lookupBidiClass d.code

def testBidiClassRegressions : Bool :=
  lookupBidiClass 0x0590 == .R
    && lookupBidiClass 0x0600 == .AN
    && lookupBidiClass 0x0860 == .AL
    && lookupBidiClass 0x10D40 == .AN
    && lookupBidiClass 0xFFFF == .BN

def testBidiMirrored (d : UnicodeData) : Bool :=
  d.bidiMirrored == lookupBidiMirrored d.code

def testCanonicalCombiningClass (d : UnicodeData) : Bool :=
  d.cc == lookupCanonicalCombiningClass d.code

partial def testCanonicalDecompositionMapping (d : UnicodeData) : Bool :=
  let m := lookupCanonicalDecompositionMapping d.code
  let l := match d.decomp with
    | some { tag := none, mapping := l, .. } => mapping (l.map Char.val)
    | _ => [d.code]
  m == l
where
  mapping : List UInt32 → List UInt32
  | [] => unreachable!
  | c :: cs =>
    let d := getUnicodeData! c
    match d.decomp with
    | some { tag := none, mapping := l, .. } => mapping <| l.map Char.val ++ cs
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

def testBlockNameRoundtrip (d : UnicodeData) : Bool :=
  BlockNameOrNoBlock.ofString? (Blocks.lookupName d.code) == some (lookupBlockName d.code)

def testBlockName : Bool :=
  getBlockName 'A' == "Basic Latin"
    && getBlockName '(' == "Basic Latin"

def testEastAsianWidthRoundtrip (d : UnicodeData) : Bool :=
  EastAsianWidth.lookup d.code == lookupEastAsianWidth d.code

def testEastAsianWidth : Bool :=
  getEastAsianWidth 'A' == EastAsianWidth.narrow
    && getEastAsianWidth '中' == EastAsianWidth.wide

def testVerticalOrientationRoundtrip (d : UnicodeData) : Bool :=
  VerticalOrientation.lookup d.code == lookupVerticalOrientation d.code

def testVerticalOrientation : Bool :=
  getVerticalOrientation 'A' == VerticalOrientation.rotated
    && getVerticalOrientation '中' == VerticalOrientation.upright

def testBidiPairedBracketRoundtrip (d : UnicodeData) : Bool :=
  BidiBrackets.lookupPairedBracket? d.code == lookupBidiPairedBracket? d.code
    && BidiBrackets.lookupPairedBracketType? d.code == lookupBidiPairedBracketType? d.code

def testBidiPairedBracket : Bool :=
  getBidiPairedBracket? '(' == some (')'.val)
    && getBidiPairedBracketType? '(' == some BidiBracketType.openBracket
    && getBidiPairedBracket? ')' == some ('('.val)
    && getBidiPairedBracketType? ')' == some BidiBracketType.closeBracket

def testBidiMirroringGlyphRoundtrip (d : UnicodeData) : Bool :=
  BidiMirroring.lookupGlyph? d.code == lookupBidiMirroringGlyph? d.code

def testBidiMirroringGlyph : Bool :=
  getBidiMirroringGlyph? '(' == some (')'.val)
    && getBidiMirroringGlyph? '<' == some ('>'.val)

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

def testNumericValueRegressions : Bool :=
  lookupNumericValue 0x4E00 == some (.numeric 1 none)
    && lookupNumericValue 0x4E03 == some (.numeric 7 none)
    && lookupNumericValue 0x4E07 == some (.numeric 10000 none)
    && lookupNumericValue 0x5146 == some (.numeric 1000000000000 none)

def testCaseFolding (d : UnicodeData) : Bool :=
  let expected := CaseFolding.data.findSome? fun e =>
    if e.code == d.code && (e.status == 'C' || e.status == 'F') then some e.mapping else none
  expected.getD #[] == lookupCaseFolding d.code

def testSimpleCaseFolding (d : UnicodeData) : Bool :=
  let expected := CaseFolding.data.findSome? fun e =>
    if e.code == d.code && (e.status == 'C' || e.status == 'S') && e.mapping.size == 1 then
      some e.mapping[0]!
    else
      none
  expected.getD d.code == lookupSimpleCaseFolding d.code

def testGraphemeBreak (d : UnicodeData) : Bool :=
  let expected := lookupRangeOpt? d.code BreakProperties.data.graphemeBreak
  let expVal := expected.map (fun s => MaybeGraphemeClusterBreak.nonOther (GraphemeClusterBreak.ofAbbrev! s.toSlice)) |>.getD .other
  expVal == lookupGraphemeClusterBreak d.code

def testWordBreak (d : UnicodeData) : Bool :=
  let expected := lookupRangeOpt? d.code BreakProperties.data.wordBreak
  expected.map (fun s => MaybeWordBreak.ofAbbrev! s.toSlice) |>.getD .other
    == lookupWordBreak d.code

def testSentenceBreak (d : UnicodeData) : Bool :=
  let expected := lookupRangeOpt? d.code BreakProperties.data.sentenceBreak
  let expVal := expected.map (fun s => MaybeSentenceBreak.nonOther (SentenceBreak.ofAbbrev! s.toSlice)) |>.getD .other
  expVal == lookupSentenceBreak d.code

def testLineBreak (d : UnicodeData) : Bool :=
  let expected := lookupRangeOpt? d.code BreakProperties.data.lineBreak
  expected.map (fun s => LineBreak.ofAbbrev! s.toSlice) |>.getD .unknown
    == lookupLineBreak d.code

def testScript (d : UnicodeData) : Bool :=
  let expected := Scripts.data.toArray.findSome? fun (sc, ranges) =>
    if ranges.any (inClosedRange d.code) then
      some (Script.ofAbbrev! (PropertyValueAliases.getShortName! "sc" sc).copy.toSlice)
    else
      none
  expected.map MaybeUnknownScript.ofScript |>.getD default == lookupScript d.code

def testScriptCodeValidation : Bool :=
  decide (Script.IsValidCodePoint Script.CodePoints.latin)
    && !decide (Script.IsValidCodePoint Script.CodePoints.unknown)
    && decide (Script.IsValidMaybeUnknownCodePoint Script.CodePoints.unknown)
    && Script.ofAbbrev? "Latn" == some (Script.ofAbbrev! "Latn")
    && Script.ofAbbrev? "Qqqq" == none

def testScriptExtensions (d : UnicodeData) : Bool :=
  let expected := lookupRange? d.code <| Id.run do
    let mut rows := #[]
    let stream := UCDStream.ofString ScriptExtensions.txt
    for record in stream do
      let (c₀, c₁) : UInt32 × UInt32 :=
        match record[0]!.split ".." |>.toList with
        | [c] => (ofHexString! c, ofHexString! c)
        | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
        | _ => panic! "invalid record in ScriptExtensions.txt"
      let scripts := (record[1]!.split " ").toArray.map Script.ofAbbrev!
      rows := rows.push (c₀, c₁, scripts)
    return rows
  expected.getD #[] == lookupScriptExtensions d.code

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

def itPropertyForData (name : String) (f : UnicodeData → Bool) (focus : Bool := false) (timeoutMs? : Option Std.Time.Millisecond.Offset := none) : Spec.Spec := do
  Spec.it (focus := focus) (timeoutMs? := timeoutMs?) name do
    let stream : UnicodeDataStream := {}
    let mut failedCodes : Array UInt32 := #[]
    for d in stream do
      if !f d then
        failedCodes := failedCodes.push d.code
    if !failedCodes.isEmpty then
      Spec.Assert.fail s!"UnicodeTableTest.{name} failed, {failedCodes.size} codes: {failedCodes}"

def itPropertySimple (name : String) (b : Bool) : Spec.Spec := do
  Spec.it name do
    if !b then
      Spec.Assert.fail s!"UnicodeTableTest.{name} failed"

public def spec : Spec.Spec := do
  Spec.describe "UnicodeTableTest" do
    itPropertyForData "Bidi_Class" testBidiClass
    itPropertySimple "Bidi_Class regressions" testBidiClassRegressions
    itPropertyForData "Block roundtrip" testBlockNameRoundtrip
    itPropertySimple "Block" testBlockName
    itPropertyForData "East_Asian_Width roundtrip" testEastAsianWidthRoundtrip
    itPropertySimple "East_Asian_Width" testEastAsianWidth
    itPropertyForData "Vertical_Orientation roundtrip" testVerticalOrientationRoundtrip
    itPropertySimple "Vertical_Orientation" testVerticalOrientation
    itPropertyForData "Bidi_Mirroring_Glyph roundtrip" testBidiMirroringGlyphRoundtrip
    itPropertySimple "Bidi_Mirroring_Glyph" testBidiMirroringGlyph
    itPropertyForData "Alphabetic" testAlphabetic
    itPropertyForData "Bidi_Paired_Bracket roundtrip" testBidiPairedBracketRoundtrip
    itPropertySimple "Bidi_Paired_Bracket" testBidiPairedBracket
    itPropertyForData "Bidi_Mirrored" testBidiMirrored
    itPropertyForData "Canonical_Combining_Class" testCanonicalCombiningClass
    itPropertyForData "Canonical_Decomposition_Mapping" testCanonicalDecompositionMapping
    itPropertyForData "Case_Mapping" testCaseMapping
    itPropertyForData "Case_Folding" testCaseFolding
    itPropertyForData "Cased" testCased
    itPropertyForData "Decomposition_Mapping" testDecompositionMapping
    itPropertyForData "Default_Ignorable_Code_Point" testDefautlIgnorableCodePoint
    itPropertyForData "Dash" testDash
    itPropertyForData "Diacritic" testDiacritic
    itPropertyForData "Emoji" testEmoji
    itPropertyForData "Emoji_Component" testEmojiComponent
    itPropertyForData "Emoji_Modifier" testEmojiModifier
    itPropertyForData "Emoji_Modifier_Base" testEmojiModifierBase
    itPropertyForData "Emoji_Presentation" testEmojiPresentation
    itPropertyForData "Extended_Pictographic" testExtendedPictographic
    itPropertyForData "Extender" testExtender
    itPropertyForData "Grapheme_Base" testGraphemeBase
    itPropertyForData "Grapheme_Break" testGraphemeBreak
    itPropertyForData "Grapheme_Extend" testGraphemeExtend
    itPropertyForData "Hyphen" testHyphen
    itPropertyForData "ID_Continue" testIDContinue
    itPropertyForData "ID_Start" testIDStart
    itPropertyForData "Lowercase" testLowercase
    itPropertyForData "Math" testMath
    itPropertyForData "Name" testName
    itPropertyForData "Noncharacter_Code_Point" testNoncharacterCodePoint
    itPropertyForData "Pattern_Syntax" testPatternSyntax
    itPropertyForData "Pattern_White_Space" testPatternWhiteSpace
    itPropertyForData "Quotation_Mark" testQuotationMark
    itPropertyForData "Regional_Indicator" testRegionalIndicator
    itPropertyForData "Sentence_Terminal" testSentenceTerminal
    itPropertyForData "Terminal_Punctuation" testTerminalPunctuation
    itPropertyForData "Titlecase" testTitlecase
    itPropertyForData "Uppercase" testUppercase
    itPropertyForData "XID_Continue" testXIDContinue
    itPropertyForData "XID_Start" testXIDStart
    itPropertyForData "Numeric_Value" testNumericValue
    itPropertySimple "Numeric_Value regressions" testNumericValueRegressions
    itPropertyForData "Script" testScript
    itPropertySimple "Script code validation" testScriptCodeValidation
    itPropertyForData "Script_Extensions" testScriptExtensions
    itPropertyForData "Sentence_Break" testSentenceBreak
    itPropertyForData "Simple_Case_Folding" testSimpleCaseFolding
    itPropertyForData "General_Category" testGeneralCategory
    itPropertyForData (timeoutMs? := some (Std.Time.Millisecond.Offset.ofSeconds (120 : Std.Time.Second.Offset))) "Line_Break" testLineBreak
    itPropertyForData "White_Space" testWhiteSpace
    itPropertyForData "Word_Break" testWordBreak
