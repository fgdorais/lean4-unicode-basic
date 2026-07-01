/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Hangul
public import UnicodeBasic.Types
public import UnicodeData.Basic
public import UnicodeData.Extracted.DerivedName
import UnicodeData.Extracted.DerivedBidiClass
import UnicodeData.Extracted.DerivedCombiningClass
import UnicodeData.Extracted.DerivedBinaryProperties
public import UnicodeData.Extracted.DerivedGeneralCategory
import UnicodeData.Extracted.DerivedLineBreak
public import UnicodeData.Extracted.DerivedNumericType
public import UnicodeData.Extracted.DerivedNumericValues

namespace Unicode

namespace CLib

@[extern "unicode_case_lookup"]
protected opaque lookupCase (c : UInt32) : UInt64

protected abbrev oUpper : UInt64 := 0x100000000
protected abbrev oLower : UInt64 := 0x200000000
protected abbrev oAlpha : UInt64 := 0x400000000
protected abbrev oMath  : UInt64 := 0x800000000

@[extern "unicode_prop_lookup"]
protected opaque lookupProp (c : UInt32) : UInt64

@[extern "unicode_script_lookup"]
protected opaque lookupScript (c : UInt32) : Script

end CLib

/-- Binary search -/
@[specialize]
private partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

/-- Parse a simple table -/
private def parseTable (s : String) (f : UInt32 → Array String.Slice → α) : Thunk <| Array (UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let val := f start record[1:]
    r := r.push (start, val)
  return r.qsort fun a b => a.1 < b.1

/-- Parse a range compressed data table -/
private def parseDataTable (s : String) (f : UInt32 → UInt32 → Array String.Slice → α) : Thunk <| Array (UInt32 × UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    let val := f start stop record[2:]
    r := r.push (start, stop, val)
  return r.qsort fun a b => a.1 < b.1

/-- Parse a range compressed property table -/
private def parsePropTable (s : String) : Thunk <| Array (UInt32 × UInt32) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    r := r.push (start, stop)
  return r.qsort fun a b => a.1 < b.1

/-- Get bidirectional class using lookup table

  Unicode property: `Bidi_Class` -/
public def lookupBidiClass (c : UInt32) : BidiClass :=
  lookupDerivedBidiClass c

/-- Get canonical combining class using lookup table

  Unicode property: `Canonical_Combining_Class` -/
public def lookupCanonicalCombiningClass (c : UInt32) : Nat :=
  lookupDerivedCombiningClass c

/-- Get canonical decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
public def lookupCanonicalDecompositionMapping (c : UInt32) : List UInt32 :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => [s.getLChar.val, s.getVChar.val, t.val]
    | none => [s.getLChar.val, s.getVChar.val]
  else
    let table := table.get
    if c < table[0]!.1 then [c] else
      match table[find c (fun i => table[i]!.1) 0 table.usize]! with
      | (v, l) => if c == v then l else [c]
where
  str : String := include_str "../data/table/Canonical_Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × List UInt32) :=
    parseTable str fun _ x => (x.map ofHexString!).toList

/-- Get simple case mappings of a code point using lookup table

  Unicode properties:
    `Simple_Lowercase_Mapping`
    `Simple_Uppercase_Mapping`
    `Simple_Titlecase_Mapping` -/
public def lookupCaseMapping (c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let v : UInt64 := CLib.lookupCase c
  if v == 0 then (c, c, c) else
    let cu : UInt32 := v.toUInt32 &&& 0x001FFFFF
    let cl : UInt32 := (v >>> 21).toUInt32 &&& 0x001FFFFF
    let ct : UInt32 := (v >>> 42).toUInt32 &&& 0x001FFFFF
    (cu, cl, ct)

/-- Get decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type` -/
public def lookupDecompositionMapping? (c : UInt32) : Option DecompositionMapping :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => some ⟨none, [s.getLVChar, t]⟩
    | none => some ⟨none, [s.getLChar, s.getVChar]⟩
  else
    let table := table.get
    if c < table[0]!.1 then none else
      match table[find c (fun i => table[i]!.1) 0 table.usize]! with
      | (v, t, l) =>
        if c == v then
          some <| .mk t (l.map fun c => Char.ofNat c.toNat).toList
        else
          none
where
  str : String := include_str "../data/table/Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × Option CompatibilityTag × Array UInt32) :=
    parseTable str fun _ x =>
      let tag :=
        if x[0]! == "" then none
        else if x[0]! == "<font>" then some .font
        else if x[0]! == "<noBreak>" then some .noBreak
        else if x[0]! == "<initial>" then some .initial
        else if x[0]! == "<medial>" then some .medial
        else if x[0]! == "<final>" then some .final
        else if x[0]! == "<isolated>" then some .isolated
        else if x[0]! == "<circle>" then some .circle
        else if x[0]! == "<super>" then some .super
        else if x[0]! == "<sub>" then some .sub
        else if x[0]! == "<vertical>" then some .vertical
        else if x[0]! == "<wide>" then some .wide
        else if x[0]! == "<narrow>" then some .narrow
        else if x[0]! == "<small>" then some .small
        else if x[0]! == "<square>" then some .square
        else if x[0]! == "<fraction>" then some .fraction
        else if x[0]! == "<compat>" then some .compat
        else panic! s!"invalid compatibility tag {x[0]!.copy}"
      (tag, x[1:].toArray.map ofHexString!)

/-- Get general category of a code point using lookup table

  Unicode property: `General_Category` -/
@[inline]
public def lookupGC (c : UInt32) : GC := lookupDerivedGeneralCategory c

/-- Get name of a code point using lookup table

  Unicode property: `Name` -/
public def lookupName (c : UInt32) : String :=
  match lookupDerivedName? c with
  | some n => n
  | none =>
    let table := table.get
    if c < table[0]!.1 then unreachable! else
      match table[find c (fun i => table[i]!.1) 0 table.usize]! with
      | (_, v, d) =>
        if c ≤ v then
          if Char.ofUInt8 (d.getUTF8Byte! 0) == '<' then
            if d == "<Control>" then
              s!"<control-{toHexStringRaw c}>"
            else if d == "<Private Use>" then
              s!"<private-use-{toHexStringRaw c}>"
            else if d == "<Reserved>" then
              s!"<reserved-{toHexStringRaw c}>"
            else if d == "<Surrogate>" then
              s!"<surrogate-{toHexStringRaw c}>"
            else if d == "<CJK Unified Ideograph>" then
              "CJK UNIFIED IDEOGRAPH-" ++ toHexStringRaw c
            else if d == "<CJK Compatibility Ideograph>" then
              "CJK COMPATIBILITY IDEOGRAPH-" ++ toHexStringRaw c
            else if d == "<Hangul Syllable>" then
              "HANGUL SYLLABLE " ++ (Hangul.getSyllable! c).getShortName
            else if d == "<Khitan Small Script Character>" then
              "KHITAN SMALL SCRIPT CHARACTER-" ++ toHexStringRaw c
            else if d == "<Nushu Character>" then
              "NUSHU CHARACTER-" ++ toHexStringRaw c
            else if d == "<Tangut Component>" then
              let i := if c.toNat < 0x18B00 then
                  -- Tangut Component
                  toString <| c.toNat - 0x18800 + 1
                else
                  -- Tangut Component Supplement
                  toString <| c.toNat - 0x18D80 + 769
              let i :=
                if i.length == 1 then "00" ++ i
                else if i.length == 2 then "0" ++ i
                else i
              "TANGUT COMPONENT-" ++ i
            else if d == "<Tangut Ideograph>" then
              "TANGUT IDEOGRAPH-" ++ toHexStringRaw c
            else panic! s!"unknown name range {d.copy}"
          else String.Slice.copy d
        else s!"<noncharacter-{toHexStringRaw c}>"
where
  str : String := include_str "../data/table/Name.txt"
  table : Thunk <| Array (UInt32 × UInt32 × String.Slice) :=
    parseDataTable str fun _ _ x => x[0]!

/-- Get numeric value of a code point using lookup table

  Unicode properties:
    `Numeric_Type`
    `Numeric_Value` -/
public def lookupNumericValue (c : UInt32) : Option NumericType :=
  let d := getUnicodeData! c
  match d.numeric with
  | some n => some n
  | none => lookupDerivedNumericValue c

/-- Get other properties using lookup table

  Unicode properties: `Other_Alphabetic`, `Other_Lowercase`, `Other_Uppercase`, `Other_Math` -/
public def lookupOther (c : UInt32) : UInt32 :=
  CLib.lookupProp c >>> 32 |>.toUInt32

/-! Properties -/

/-- Check if code point is alphabetic using lookup table

  Unicode property: `Alphabetic` -/
@[inline]
public def lookupAlphabetic (c : UInt32) : Bool :=
  let m := CLib.oAlpha ||| (GC.L ||| GC.Nl).toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is bidi mirrored using lookup table

  Unicode property: `Bidi_Mirrored`
-/
public def lookupBidiMirrored (c : UInt32) : Bool :=
  lookupDerivedBidiMirrored c

/-- Check if code point is a cased letter using lookup table

  Unicode property: `Cased` -/
@[inline]
public def lookupCased (c : UInt32 ) : Bool :=
  let m := CLib.oUpper ||| CLib.oLower ||| GC.LC.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is ignorable using lookup table

  Unicode property: `Default_Ignorable_Code_Point` -/
@[inline]
public def lookupDefaultIgnorableCodePoint (c : UInt32 ) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Default_Ignorable_Code_Point.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a lowercase letter using lookup table

  Unicode property: `Lowercase` -/
@[inline]
public def lookupLowercase (c : UInt32) : Bool :=
  let m := CLib.oLower ||| GC.Ll.toUInt64
  CLib.lookupProp c &&& m != 0


/-- Check if code point is a mathematical symbol using lookup table

  Unicode property: `Math` -/
@[inline]
public def lookupMath (c : UInt32) : Bool :=
  let m := CLib.oMath ||| GC.Sm.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is a noncharcter code point

  Unicode property: `Noncharacter_Code_Point` -/
@[inline]
public def lookupNoncharacterCodePoint (c : UInt32) : Bool :=
  (c ≤ 0xFDEF && 0xFDD0 ≤ c) || (c ≤ Unicode.max && c &&& 0xFFFE == 0xFFFE)

/-- Check if code point is a titlecase letter using lookup table

  Unicode property: `Titlecase` -/
@[inline]
public def lookupTitlecase (c : UInt32) : Bool :=
  lookupGC c == GC.Lt

/-- Check if code point is a uppercase letter using lookup table

  Unicode property: `Uppercase` -/
@[inline]
public def lookupUppercase (c : UInt32) : Bool :=
  let m := CLib.oUpper ||| GC.Lu.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is a white space character using lookup table

  Unicode property: `White_Space` -/
public def lookupWhiteSpace (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/White_Space.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Get the script of a code point using lookup table

  Unicode property: `Script` -/
@[inline]
public def lookupScript (c : UInt32) : Script := CLib.lookupScript c

/-- Get the name of a script

  Unicode property: `Script` -/
public def lookupScriptName (s : Script) : Option String.Slice :=
  let table := table.get
  if s.code < table[0]!.1 then none else
    match table[find s.code (fun i => table[i]!.1) 0 table.usize]! with
    | (c, v) => if s.code = c then some v else none
where
  str : String := include_str "../data/table/Script_Name.txt"
  table : Thunk <| Array (UInt32 × String.Slice) := parseTable str fun _ n => n[0]!

/-- Get script extensions of a code point using lookup table

  Unicode property: `Script_Extensions` -/
public def lookupScriptExtensions (c : UInt32) : Array Script :=
  let table := table.get
  if c < table[0]!.1 then #[] else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v, scs) =>
      if c ≤ v then
        scs
      else
        #[]
where
  str : String := include_str "../data/table/Script_Extensions.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Array Script) :=
    parseDataTable str fun _ _ x =>
      x[0]!.split " " |>.toArray.map Script.ofAbbrev!

/-- Check if code point has ID_Start property using lookup table -/
public def lookupIDStart (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/ID_Start.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has ID_Continue property using lookup table -/
public def lookupIDContinue (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/ID_Continue.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has XID_Start property using lookup table -/
public def lookupXIDStart (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/XID_Start.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has XID_Continue property using lookup table -/
public def lookupXIDContinue (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/XID_Continue.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Dash property using lookup table -/
public def lookupDash (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Dash.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Hyphen property using lookup table -/
public def lookupHyphen (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Hyphen.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Quotation_Mark property using lookup table -/
public def lookupQuotationMark (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Quotation_Mark.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Terminal_Punctuation property using lookup table -/
public def lookupTerminalPunctuation (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Terminal_Punctuation.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Extender property using lookup table -/
public def lookupExtender (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Extender.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Regional_Indicator property using lookup table -/
public def lookupRegionalIndicator (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Regional_Indicator.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Get case folding of a code point using lookup table -/
public def lookupCaseFolding (c : UInt32) : Array UInt32 :=
  let table := table.get
  if c < table[0]!.1 then #[] else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (v, m) => if c == v then m else #[]
where
  str : String := include_str "../data/table/Case_Folding.txt"
  table : Thunk <| Array (UInt32 × Array UInt32) :=
    parseTable str fun _ x => x[0]!.split ";" |>.toArray.map ofHexString!

/-- Get simple case folding of a code point using lookup table -/
public def lookupSimpleCaseFolding (c : UInt32) : UInt32 :=
  let table := table.get
  if c < table[0]!.1 then c else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (v, m) => if c == v then m else c
where
  str : String := include_str "../data/table/Simple_Case_Folding.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parseTable str fun _ x => ofHexString! x[0]!

/-- Get grapheme cluster break property using lookup table -/
public def lookupGraphemeClusterBreak (c : UInt32) : GraphemeClusterBreak :=
  let table := table.get
  if c < table[0]!.1 then .other else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v, b) => if c ≤ v then b else .other
where
  str : String := include_str "../data/table/Grapheme_Break.txt"
  table : Thunk <| Array (UInt32 × UInt32 × GraphemeClusterBreak) :=
    parseDataTable str fun _ _ x => GraphemeClusterBreak.ofAbbrev! x[0]!

/-- Get word break property using lookup table -/
public def lookupWordBreak (c : UInt32) : WordBreak :=
  let table := table.get
  if c < table[0]!.1 then .other else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v, b) => if c ≤ v then b else .other
where
  str : String := include_str "../data/table/Word_Break.txt"
  table : Thunk <| Array (UInt32 × UInt32 × WordBreak) :=
    parseDataTable str fun _ _ x => WordBreak.ofAbbrev! x[0]!

/-- Check if code point has Diacritic property using lookup table -/
public def lookupDiacritic (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Diacritic.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Sentence_Terminal property using lookup table -/
public def lookupSentenceTerminal (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Sentence_Terminal.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Pattern_Syntax property using lookup table -/
public def lookupPatternSyntax (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Pattern_Syntax.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Pattern_White_Space property using lookup table -/
public def lookupPatternWhiteSpace (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Pattern_White_Space.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Emoji property using lookup table -/
public def lookupEmoji (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Emoji.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Emoji_Presentation property using lookup table -/
public def lookupEmojiPresentation (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Emoji_Presentation.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Emoji_Modifier property using lookup table -/
public def lookupEmojiModifier (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Emoji_Modifier.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Emoji_Modifier_Base property using lookup table -/
public def lookupEmojiModifierBase (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Emoji_Modifier_Base.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Emoji_Component property using lookup table -/
public def lookupEmojiComponent (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Emoji_Component.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Extended_Pictographic property using lookup table -/
public def lookupExtendedPictographic (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Extended_Pictographic.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Get sentence break property using lookup table -/
public def lookupSentenceBreak (c : UInt32) : SentenceBreak :=
  let table := table.get
  if c < table[0]!.1 then .other else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v, b) => if c ≤ v then b else .other
where
  str : String := include_str "../data/table/Sentence_Break.txt"
  table : Thunk <| Array (UInt32 × UInt32 × SentenceBreak) :=
    parseDataTable str fun _ _ x => SentenceBreak.ofAbbrev! x[0]!

/-- Get line break property using lookup table -/
public def lookupLineBreak (c : UInt32) : LineBreak :=
  lookupDerivedLineBreak c

/-- Check if code point has Grapheme_Base property using lookup table -/
public def lookupGraphemeBase (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Grapheme_Base.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point has Grapheme_Extend property using lookup table -/
public def lookupGraphemeExtend (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.usize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Grapheme_Extend.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

initialize _ : IO Unit := pure ()
