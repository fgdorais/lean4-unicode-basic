/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Hangul
import UnicodeBasic.Types

-- Issue: lean4#11275
namespace String.Slice

def toInt? (s : String.Slice) : Option Int :=
  if s.front? = '-' then
    Int.negOfNat <$> (s.drop 1).toNat?
  else
    Int.ofNat <$> s.toNat?

def toInt! (s : String.Slice) : Int :=
  s.toInt?.get!

end String.Slice

namespace Unicode

/-- Structure for data from `UnicodeData.txt` -/
structure UnicodeData where
  /-- Code Value -/
  code : UInt32
  /-- Character Name -/
  name : String.Slice
  /-- General Category -/
  gc : GC
  /-- Bidirectional Class -/
  bidi : BidiClass
  /-- Canonical Combining Class -/
  cc : Nat := 0
  /-- Bidirectional Mirrored -/
  bidiMirrored : Bool := false
  /-- Character Decomposition Mapping -/
  decomp : Option DecompositionMapping := none
  /-- Numeric Value -/
  numeric : Option NumericType := none
  /-- Uppercase Mapping -/
  uppercase : Option Char := none
  /-- Lowercase Mapping -/
  lowercase : Option Char := none
  /-- Titlecase Mapping -/
  titlecase : Option Char := none
deriving BEq

instance : Inhabited UnicodeData where
  default := {
    code := 0
    name := "<control-0000>"
    bidi := .BN
    gc := .Cc
  }

/-- Make `UnicodeData` for noncharacter code point -/
def UnicodeData.mkNoncharacter (code : UInt32) : UnicodeData where
  code := code
  name :=
    -- Extracted from property `Noncharacter_Code_Point`
    let isReserved := (code &&& 0xFFFFFFF0 == 0x0000FDD0) ||
                      (code &&& 0xFFFFFFF0 == 0x0000FDE0) ||
                      (code &&& 0x0000FFFE == 0x0000FFFE)
    (if isReserved then "<reserved-" else "<noncharacter-") ++ toHexStringAux code ++ ">"
  bidi := .BN
  gc := .Cn

/-- Make `UnicodeData` for generic control code point -/
def UnicodeData.mkControl (c : UInt32) : UnicodeData where
  code := c
  name := s!"<control-{toHexStringAux c}>"
  bidi := .BN
  gc := .Cc

/-- Make `UnicodeData` for generic surrogate code point -/
def UnicodeData.mkSurrogate (c : UInt32) : UnicodeData where
  code := c
  name := s!"<surrogate-{toHexStringAux c}>"
  bidi := .L
  gc := .Cs

/-- Make `UnicodeData` for generic private use code point -/
def UnicodeData.mkPrivateUse (c : UInt32) : UnicodeData where
  code := c
  name := s!"<private-use-{toHexStringAux c}>"
  bidi := .L
  gc := .Co

/-- Make `UnicodeData` for CJK compatibilty ideograph code point -/
def UnicodeData.mkCJKCompatibilityIdeograph (c : UInt32) : UnicodeData where
  code := c
  name := s!"CJK COMPATIBILITY IDEOGRAPH-{toHexStringAux c}"
  bidi := .L
  gc := .Lo

/-- Make `UnicodeData` for CJK unified ideograph code point -/
def UnicodeData.mkCJKUnifiedIdeograph (c : UInt32) : UnicodeData where
  code := c
  name := s!"CJK UNIFIED IDEOGRAPH-{toHexStringAux c}"
  bidi := .L
  gc := .Lo

/-- Make `UnicodeData` for Hangul syllable code point -/
def UnicodeData.mkHangulSyllable (c : UInt32) : UnicodeData :=
  let s := Hangul.getSyllable! c
  let m : DecompositionMapping :=
    match s.getTChar? with
    | some t => ⟨none, [s.getLVChar, t]⟩
    | none => ⟨none, [s.getLChar, s.getVChar]⟩
  { code := c
    name := s!"HANGUL SYLLABLE {s.getShortName}"
    bidi := .L
    gc := .Lo
    decomp := m
  }

/-- Make `UnicodeData` for Tangut ideograph code point -/
def UnicodeData.mkTangutIdeograph (c : UInt32) : UnicodeData where
  code := c
  name := s!"TANGUT IDEOGRAPH-{toHexStringAux c}"
  bidi := .L
  gc := .Lo

/-- Raw string from file `UnicodeData.txt` -/
protected def UnicodeData.txt := include_str "../data/UnicodeData.txt"

/-- Parse `UnicodeData.txt` -/
private unsafe def UnicodeData.init : IO (Array UnicodeData) := do
  let stream := UCDStream.ofString UnicodeData.txt
  let mut arr := #[]
  for record in stream do
    arr := arr.push {
      code := ofHexString! record[0]!
      name := record[1]!
      gc := GC.ofAbbrev! record[2]!
      cc := record[3]!.toNat!
      bidi := BidiClass.ofAbbrev! record[4]!
      decomp := getDecompositionMapping? record[5]!
      numeric := getNumericType? record[6]! record[7]! record[8]!
      bidiMirrored := record[9]! == "Y"
      uppercase := if record[12]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[12]!
      lowercase := if record[13]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[13]!
      titlecase := if record[14]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[14]!
    }
  return arr

where

  /-- Get decomposition mapping -/
  getDecompositionMapping? (s : String.Slice) : Option DecompositionMapping := do
    /-
      The value of the `Decomposition_Mapping` property for a character is
      provided in field 5 of `UnicodeData.txt`. This is a string-valued
      property, consisting of a sequence of one or more Unicode code points.
      The default value of the `Decomposition_Mapping` property is the code
      point of the character itself. The use of the default value for a
      character is indicated by leaving field 5 empty in `UnicodeData.txt`.
      Informally, the value of the `Decomposition_Mapping` property for a
      character is known simply as its decomposition mapping. When a
      character's decomposition mapping is other than the default value, the
      decomposition mapping is printed out explicitly in the names list for
      the Unicode code charts.

      The prefixed tags supplied with a subset of the decomposition mappings
      generally indicate formatting information. Where no such tag is given,
      the mapping is canonical. Conversely, the presence of a formatting tag
      also indicates that the mapping is a compatibility mapping and not a
      canonical mapping. In the absence of other formatting information in a
      compatibility mapping the tag is used to distinguish it from canonical
      mappings.
    -/
    if s.isEmpty then
      none
    else
      match s.split ' ' |>.toList with
      | t :: cs =>
        let mut tag := none
        let mut cs := cs.map fun c => Char.mkUnsafe <| ofHexString! c
        if '<' == t.front then
          tag :=
            if t == "<font>" then some CompatibilityTag.font else
            if t == "<noBreak>" then some CompatibilityTag.noBreak else
            if t == "<initial>" then some CompatibilityTag.initial else
            if t == "<medial>" then some CompatibilityTag.medial else
            if t == "<final>" then some CompatibilityTag.final else
            if t == "<isolated>" then some CompatibilityTag.isolated else
            if t == "<circle>" then some CompatibilityTag.circle else
            if t == "<super>" then some CompatibilityTag.super else
            if t == "<sub>" then some CompatibilityTag.sub else
            if t == "<vertical>" then some CompatibilityTag.vertical else
            if t == "<wide>" then some CompatibilityTag.wide else
            if t == "<narrow>" then some CompatibilityTag.narrow else
            if t == "<small>" then some CompatibilityTag.small else
            if t == "<square>" then some CompatibilityTag.square else
            if t == "<fraction>" then some CompatibilityTag.fraction else
            if t == "<compat>" then some CompatibilityTag.compat else
            none
        else
          cs := (Char.mkUnsafe <| ofHexString! t) :: cs
        some ⟨tag, cs⟩
      | [] => unreachable!

  /-- Get numeric type -/
  getNumericType? (s₁ s₂ s₃ : String.Slice) : Option NumericType := do
    /-
      If the character has the property value `Numeric_Type=Decimal`, then the
      `Numeric_Value` of that digit is represented with an integer value
      (limited to the range 0..9) in fields 6, 7, and 8. Characters with the
      property value `Numeric_Type=Decimal` are restricted to digits which can
      be used in a decimal radix positional numeral system and which are
      encoded in the standard in a contiguous ascending range 0..9. See the
      discussion of decimal digits in Chapter 4, Character Properties in the
      Unicode Standard.

      If the character has the property value `Numeric_Type=Digit`, then the
      `Numeric_Value` of that digit is represented with an integer value
      (limited to the range 0..9) in fields 7 and 8, and field 6 is null. This
      covers digits that need special handling, such as the compatibility
      superscript digits. Starting with Unicode 6.3.0, no newly encoded
      numeric characters will be given `Numeric_Type=Digit`, nor will existing
      characters with `Numeric_Type=Numeric` be changed to
      `Numeric_Type=Digit`. The distinction between those two types is not
      considered useful.

      If the character has the property value `Numeric_Type=Numeric`, then the
      `Numeric_Value` of that character is represented with a positive or
      negative integer or rational number in this field and fields 6 and 7 are
      null. This includes fractions such as, for example, "1/5" for U+2155
      VULGAR FRACTION ONE FIFTH. Some characters have these properties based
      on values from the Unihan data files. See `Numeric_Type`, Han.
    -/
    if s₁.isEmpty then
      if s₂.isEmpty then
        if s₃.isEmpty then
          none
        else
          match s₃.split "/" |>.toList with
          | [s] => -- integer value
            return .numeric s.toInt! none -- TODO: don't use toString
          | [sn,sd] => -- rational value
            return .numeric sn.toInt! (some sd.toNat!) -- TODO: don't use toString
          | _ => panic! "invalid numeric value"
      else
        return .digit <| getDigitUnsafe <| s₂.front
    else
      return .decimal <| getDigitUnsafe <| s₁.front

  /-- Get decimal digit -/
  @[inline]
  getDigitUnsafe (char : Char) : Fin 10 :=
    unsafeCast (char.val - '0'.val).toNat

/-- Parsed data from `UnicodeData.txt` -/
@[init UnicodeData.init]
protected def UnicodeData.data : Array UnicodeData := #[]

/-- Get code point data from `UnicodeData.txt` -/
partial def getUnicodeData? (code : UInt32) : Option UnicodeData := do
  if code > Unicode.max then
    none
  else if code ≤ 0x0377 then
    /-
      At time of writing, the first unassigned code point is U+0378 (decimal
      888). Also the first code range starts at U+3400. So we can skip testing
      for unassigned or code ranges for code points below 888. This is
      convenient because the smaller code points include ASCII and other
      common subsets.
    -/
    let data := UnicodeData.data[code.toUSize]!
    assert! (data.code == code)
    if data.name == "<control>" then
      return {data with
        name := s!"<control-{toHexStringAux code}>"}
    else
      return data
  else
    let data := UnicodeData.data[find 0x0377 UnicodeData.data.size]!
    /-
      For backward compatibility, ranges in the file `UnicodeData.txt` are
      specified by entries for the start and end characters of the range,
      rather than by the form "X..Y". The start character is indicated by a
      range identifier, followed by a comma and the string "First", in angle
      brackets. This entry takes the place of a regular character name in
      field 1 for that line. The end character is indicated on the next line
      with the same range identifier, followed by a comma and the string
      "Last", in angle brackets:

        4E00;<CJK Ideograph, First>;Lo;0;L;;;;;N;;;;;
        9FEF;<CJK Ideograph, Last>;Lo;0;L;;;;;N;;;;;

      For character ranges using this convention, the names of all characters
      in the range are algorithmically derivable. See Section 4.8, Name in the
      Unicode Standard for more information on derivation of character names
      for such ranges.
    -/
    if data.name.front == '<' then
      if code = data.code || data.name.takeEnd 8 == ", First>" then
        if data.name.take 16 == "<Hangul Syllable" then
          UnicodeData.mkHangulSyllable code
        else if data.name.take 14 == "<CJK Ideograph" then
          UnicodeData.mkCJKUnifiedIdeograph code
        else if data.name.take 17 == "<Tangut Ideograph" then
          UnicodeData.mkTangutIdeograph code
        else if data.gc == .Cc then
          UnicodeData.mkControl code
        else if data.gc == .Co then
          UnicodeData.mkPrivateUse code
        else if data.gc == .Cs then
          UnicodeData.mkSurrogate code
        else
          panic! "unexpected character name value"
      else
        return .mkNoncharacter code
    else if code = data.code then
      return data
    else
      return .mkNoncharacter code

where

  -- TODO: stop reinventing the wheel!
  /-- Binary search -/
  find (lo hi : Nat) : Nat :=
    assert! (hi ≤ UnicodeData.data.size)
    assert! (lo < hi)
    assert! (UnicodeData.data[lo]!.code ≤ code)
    let mid := (lo + hi) / 2 -- NB: mid < hi because lo < hi
    if lo = mid then
      mid
    else
      if code < UnicodeData.data[mid]!.code then
        find lo mid
      else
        find mid hi

@[inherit_doc getUnicodeData?]
def getUnicodeData! (code : UInt32) :=
  match getUnicodeData? code with
  | some data => data
  | none => panic! "code point out of range"

/-- Get character data from `UnicodeData.txt` -/
def getUnicodeData (char : Char) : UnicodeData :=
  match getUnicodeData? char.val with
  | some data => data
  | none => unreachable!

/-- Stream type to roll through all code points up to `Unicode.max`, yielding `UnicodeData` -/
structure UnicodeDataStream where
  code : UInt32 := 0
  index : USize := 0
  default : UInt32 → UnicodeData := UnicodeData.mkNoncharacter
  deriving Inhabited

private def UnicodeDataStream.next? (s : UnicodeDataStream) : Option (UnicodeData × UnicodeDataStream) := do
  let c := s.code
  let i := s.index
  if c > Unicode.max then
    none
  else if h : i < UnicodeData.data.size.toUSize then
    let d := UnicodeData.data[i]
    let n := d.name
    if c < d.code then
      return (s.default c, {s with code := c+1})
    else if n == "<control>" then
      let d := {d with name := s!"<control-{toHexStringAux c}>"}
      return (d, {s with code := c+1, index := i+1})
    else if n.front == '<' then
      if n.takeEnd 8 == ", First>" then
        let mut default := UnicodeData.mkNoncharacter
        if (n.dropEnd 8).takeEnd 11 == "Private Use" then
          default := UnicodeData.mkPrivateUse
        else if (n.dropEnd 8).takeEnd 9 == "Surrogate" then
          default := UnicodeData.mkSurrogate
        else if n.take 14 == "<CJK Ideograph" then
          default := UnicodeData.mkCJKUnifiedIdeograph
        else if n.take 16 == "<Hangul Syllable" then
          default := UnicodeData.mkHangulSyllable
        else if n.take 17 == "<Tangut Ideograph" then
          default := UnicodeData.mkTangutIdeograph
        else
          panic! "invalid Unicode data"
        return (default c, {s with code := c+1, index := i+1, default})
      else if n.takeEnd 7 == ", Last>" then
        return (s.default c, {s with code := c+1, index := i+1, default := UnicodeData.mkNoncharacter})
      else
        panic! "invalid Unicode data"
    else
      return (d, {s with code := c+1, index := i+1})
  else
    return (.mkNoncharacter c, {s with code := c+1})

instance : Std.Stream UnicodeDataStream UnicodeData where
  next? := UnicodeDataStream.next?

end Unicode
