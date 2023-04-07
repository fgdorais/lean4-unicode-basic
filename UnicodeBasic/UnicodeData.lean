/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Types

namespace Unicode

/-- Structure for data from `UnicodeData.txt` -/
structure UnicodeData where
  /-- Code Value -/
  codeValue : UInt32
  /-- Character Name -/
  characterName : String
  /-- General Category -/
  generalCategory : GeneralCategory
  /-- Canonical Combining Class -/
  canonicalCombiningClass : Nat
  /-- Bidirectional Class -/
  bidiClass : BidiClass
  /-- Bidirectional Mirrored -/
  bidiMirrored : Bool
  /-- Character Decomposition Mapping -/
  decompositionMapping : Option DecompositionMapping := none
  /-- Numeric Value -/
  numeric : Option NumericType := none
  /-- Uppercase Mapping -/
  uppercaseMapping : Option Char := none
  /-- Lowercase Mapping -/
  lowercaseMapping : Option Char := none
  /-- Titlecase Mapping -/
  titlecaseMapping : Option Char := none
deriving Repr, Inhabited

/-- Make `UnicodeData` for noncharacter code point -/
def UnicodeData.mkNoncharacter (code : UInt32) : UnicodeData where
  codeValue := code
  generalCategory := .Cn
  characterName :=
    -- Extracted from `PropLists.txt`
    let isReserved := (code &&& 0xFFFFFFF0 == 0x0000FDD0) ||
                      (code &&& 0xFFFFFFF0 == 0x0000FDE0) ||
                      (code &&& 0x0000FFFE) == 0x0000FFFE
    (if isReserved then "<reserved-" else "<noncharacter-") ++ toHexStringAux code ++ ">"
  canonicalCombiningClass := 0
  bidiClass := .BN
  bidiMirrored := false

/-- Raw string from file `UnicodeData.txt` -/
protected def UnicodeData.txt := include_str "../data/UnicodeData.txt"

/-- Parse `UnicodeData.txt` -/
private unsafe def UnicodeData.init : IO (Array UnicodeData) := do
  let stream := UCDStream.ofString UnicodeData.txt
  let mut arr := #[]
  for record in stream do
    arr := arr.push {
      codeValue := ofHexString! record[0]!
      characterName := record[1]!
      generalCategory := GeneralCategory.ofAbbrev! record[2]!
      canonicalCombiningClass := record[3]!.toNat!
      bidiClass := BidiClass.ofAbbrev! record[4]!
      decompositionMapping := getDecompositionMapping? record[5]!
      numeric := getNumericType? record[6]! record[7]! record[8]!
      bidiMirrored := record[9]! == "Y"
      uppercaseMapping := if record[12]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[12]!
      lowercaseMapping := if record[13]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[13]!
      titlecaseMapping := if record[14]!.isEmpty then none else some <| Char.mkUnsafe <| ofHexString! record[14]!
    }
  return arr

where

  /-- Get decomposition mapping -/
  getDecompositionMapping? (s : String) : Option DecompositionMapping := do
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
      match s.splitOn " " with
      | t :: cs =>
        let mut tag := none
        let mut cs := cs.map fun c => Char.mkUnsafe <| ofHexString! c
        if "<".isPrefixOf t then
          -- compatibility mapping
          tag := match t with
          | "<font>" => some CompatibilityTag.font
          | "<noBreak>" => some CompatibilityTag.noBreak
          | "<initial>" => some CompatibilityTag.initial
          | "<medial>" => some CompatibilityTag.medial
          | "<final>" => some CompatibilityTag.final
          | "<isolated>" => some CompatibilityTag.isolated
          | "<circle>" => some CompatibilityTag.circle
          | "<super>" => some CompatibilityTag.super
          | "<sub>" => some CompatibilityTag.sub
          | "<vertical>" => some CompatibilityTag.vertical
          | "<wide>" => some CompatibilityTag.wide
          | "<narrow>" => some CompatibilityTag.narrow
          | "<small>" => some CompatibilityTag.narrow
          | "<square>" => some CompatibilityTag.narrow
          | "<fraction>" => some CompatibilityTag.fraction
          | "<compat>"=> some CompatibilityTag.compat
          | _ => panic! "invalid compatibility tag"
        else
          -- canonical mapping
          cs := (Char.mkUnsafe <| ofHexString! t) :: cs
        some ⟨tag, cs⟩
      | [] => unreachable!

  /-- Get numeric type -/
  getNumericType? (s₁ s₂ s₃ : String) : Option NumericType := do
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
          match s₃.splitOn "/" with
          | [s] => -- integer value
            return .numeric s.toInt! none
          | [sn,sd] => -- rational value
            return .numeric sn.toInt! (some sd.toNat!)
          | _ => panic! "invalid numeric value"
      else
        return .digit <| getDigitUnsafe <| s₂.get! 0
    else
      return .decimal <| getDigitUnsafe <| s₁.get! 0

  /-- Get decimal digit -/
  @[inline]
  getDigitUnsafe (char : Char) : Fin 10 :=
    unsafeCast (char.val - '0'.val).toNat

/-- Parsed data from `UnicodeData.txt` -/
@[init UnicodeData.init]
protected def UnicodeData.data : Array UnicodeData := #[]

/-- Get Hangul syllable name -/
def getHangulSyllableName? (code : UInt32) : Option String :=
    -- See Unicode Standard 3.12
    if code < 0xAC00 then none else
      let SIndex := (code - 0xAC00).toNat
      if SIndex ≥ JamoL.size * JamoV.size * JamoT.size then none else
        -- NB: SIndex < JamoL.size * JamoV.size * JamoT.size
        let LIndex := SIndex / (JamoV.size * JamoT.size) -- NB: LIndex < JamoL.size
        let NIndex := SIndex % (JamoV.size * JamoT.size) -- NB: NIndex < JamoV.size * JamoT.size
        let VIndex := NIndex / JamoT.size -- NB: VIndex < JamoV.size
        let TIndex := NIndex % JamoT.size -- NB: TIndex < JamoT.size
        return "HANGUL SYLLABLE " ++ JamoL[LIndex]! ++ JamoV[VIndex]! ++ JamoT[TIndex]!

where

  /-- Extracted from `Jamo.txt` -/
  JamoL := #["G", "GG", "N", "D", "DD", "R", "M", "B", "BB", "S", "SS", "", "J", "JJ", "C", "K", "T", "P", "H"]

  /-- Extracted from `Jamo.txt` -/
  JamoV := #["A", "AE", "YA", "YAE", "EO", "E", "YEO", "YE", "O", "WA", "WAE", "OE", "YO", "U", "WEO", "WE", "WI", "YU", "EU", "YI", "I"]

  /-- Extracted from `Jamo.txt` -/
  JamoT := #["", "G", "GG", "GS", "N", "NJ", "NH", "D", "L", "LG", "LM", "LB", "LS", "LT", "LP", "LH", "M", "B", "BS", "S", "SS", "NG", "J", "C", "K", "T", "P", "H"]

@[inherit_doc getHangulSyllableName?]
def getHangulSyllableName! (code : UInt32) : String :=
  match getHangulSyllableName? code with
  | some str => str
  | none => panic! "invalid Hangul syllable code point"

/-- Get code point data from `UnicodeData.txt` -/
partial def getUnicodeData? (code : UInt32) : Option UnicodeData := do
  if code > Unicode.max then
    none
  else if code < 888 then
    /-
      At time of writing, the first unassigned code point is U+0378 (decimal
      888). Also the first code range starts at U+3400. So we can skip testing
      for unassigned or code ranges for code points below 888. This is
      convenient because the smaller code points include ASCII and other
      common subsets.
    -/
    let data := UnicodeData.data[find 0 888]!
    assert! (data.codeValue = code)
    if "<".isPrefixOf data.characterName then
      assert! (data.characterName = "<control>")
      return {data with characterName := "<control-" ++ toHexStringAux code ++ ">"}
    else
      return data
  else
    let data := UnicodeData.data[find 888 UnicodeData.data.size]!
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
    if "<".isPrefixOf data.characterName then
      if code = data.codeValue || data.characterName.endsWith ", First>" then
        if "<Hangul Syllable".isPrefixOf data.characterName then
          return {data with
            codeValue := code
            characterName := getHangulSyllableName! code
          }
        else if "<CJK Ideograph".isPrefixOf data.characterName then
          return {data with
            codeValue := code
            characterName := "CJK UNIFIED IDEOGRAPH-" ++ toHexStringAux code
          }
        else if "<Tangut Ideograph".isPrefixOf data.characterName then
          return {data with
            codeValue := code
            characterName := "TANGUT IDEOGRAPH-" ++ toHexStringAux code
          }
        else
          match data.generalCategory with
          | ⟨.other, some .privateUse⟩ =>
            return {data with
              codeValue := code
              characterName := "<private-use-" ++ toHexStringAux code ++ ">"
            }
          | ⟨.other, some .surrogate⟩ =>
            return {data with
              codeValue := code
              characterName := "<surrogate-" ++ toHexStringAux code ++ ">"
            }
          | _ => panic! "unexpected character name value"
      else
        return .mkNoncharacter code
    else if code = data.codeValue then
      return data
    else
      return .mkNoncharacter code

where

  /-- Binary search -/
  find (lo hi : Nat) : Nat :=
    assert! (hi ≤ UnicodeData.data.size)
    assert! (lo < hi)
    assert! (UnicodeData.data[lo]!.codeValue ≤ code)
    let mid := (lo + hi) / 2 -- NB: mid < hi because lo < hi
    if lo = mid then
      mid
    else
      if code < UnicodeData.data[mid]!.codeValue then
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

end Unicode
