/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.Types
import UnicodeBasic.TableLookup

/-!
  # General API #

  As a general rule, for a given a Unicode property called `Unicode_Property`,
  for example:

  - If the property is boolean valued then the implementation is called
    `Unicode.isUnicodeProperty`.

  - Otherwise, the implementation is called `Unicode.getUnicodeProperty`.

  - If the value is not of standard type (`Bool`, `Char`, `Nat`, `Int`, etc.)
    or a combination thereof (e.g. `Bool × Option Nat`) then the value type is
    defined in `UnicodeBasic.Types`.

  - If the input type needs disambiguation (e.g. `Char` vs `String`) the type
    name may be appended to the name as in `Unicode.isUnicodePropertyChar` or
    in `Unicode.getUnicodePropertyString`.

  - If the output type is `Option _` then the suffix `?` may be appended to
    indicate that this is a partial function. In this case, a companion
    function with the suffix `!` may be implemented. This function will
    perform the same calculation as the original but it assumes the user has
    checked that the input is in the domain, the function may panic if this
    is not the case.

  There are exceptions and variations on these general rules. For example,
  `Unicode.isInGeneralCategory` checks whether a character belongs to a given
  general category. Because of derived general categories, this makes more
  sense than what the first rule above would give.

  Some properties may be grouped in a namespace. The namespace
  `Unicode.GeneralCategory` is such. For example, `Unicode.GeneralCategory.isL`
  checks whether a character belongs to the derived general category `L`.
-/

namespace Unicode

/-!
  ## Name ##
-/

/-- Get character name

  When the Unicode property `Name` is empty, a unique code label is returned
  as described in Unicode Standard, section 4.8. These labels start with
  `'<'` (U+003C) and end with `'>'` (U+003E) so they are distinguishable from
  actual name values.

  Unicode property: `Name`
-/
@[inline]
def getName (char : Char) : String := lookupName char.val

/-!
  ## Bidirectional Properties ##
-/

/-- Get character bidirectional class

  Unicode property: `Bidi_Class` -/
@[inline]
def getBidiClass (char : Char) : BidiClass := lookupBidiClass char.val

/-- Check if bidirectional mirrored character

  Unicode property: `Bidi_Mirrored` -/
@[inline]
def isBidiMirrored (char : Char) : Bool := lookupBidiMirrored char.val

/-- Check if bidirectional control character

  Unicode property: `Bidi_Control` -/
@[inline]
def isBidiControl (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val == 0x061C
  || char.val <= 0x200F && char.val >= 0x200E
  || char.val <= 0x202E && char.val >= 0x202A
  || char.val <= 0x2069 && char.val >= 0x2066

/-!
  ## General Category ##
-/

/-- Get character general category

  *Caveat*: This function never returns a derived general category. Use
  `Unicode.isInGeneralCategory` to check whether a character belongs to a
  general category (derived or not).

  Unicode property: `General_Category` -/
@[inline]
def getGeneralCategory (char : Char) : GeneralCategory := lookupGeneralCategory char.val

/-- Check if character belongs to the general category

  Unicode property: `General_Category` -/
@[inline]
def isInGeneralCategory (char : Char) (category : GeneralCategory) : Bool :=
  match category, getGeneralCategory char with
  | ⟨major, none⟩, ⟨charMajor, _⟩ => major = charMajor
  | ⟨_, some .casedLetter⟩, ⟨_, some .lowercaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, ⟨_, some .titlecaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, ⟨_, some .uppercaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, _ => false
  | cat, charCat => cat = charCat

namespace GeneralCategory

/-- Check if letter character (`L`)

  This is a derived category (`L = Lu | Ll | Lt | Lm | Lo`).

  Unicode Property: `General_Category=L` -/
@[inline]
def isLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.letter, _⟩ => true
  | _ => false

@[inherit_doc isLetter]
protected abbrev isL := isLetter

/-- Check if lowercase letter character (`Ll`)

  Unicode Property: `General_Category=Ll` -/
@[inline]
def isLowercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | _ => false

@[inherit_doc isLowercaseLetter]
protected abbrev isLl := isLowercaseLetter

/-- Check if titlecase letter character (`Lt`)

  Unicode Property: `General_Category=Lt` -/
@[inline]
def isTitlecaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .titlecaseLetter⟩ => true
  | _ => false

@[inherit_doc isTitlecaseLetter]
protected abbrev isLt := isTitlecaseLetter

/-- Check if uppercase letter character (`Lu`)

  Unicode Property: `General_Category=Lu` -/
@[inline]
def isUppercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

@[inherit_doc isUppercaseLetter]
protected abbrev isLu := isUppercaseLetter

/-- Check if cased letter character (`LC`)

  This is a derived category (`L = Lu | Ll | Lt`).

  Unicode Property: `General_Category=LC` -/
@[inline]
def isCasedLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | ⟨_, some .titlecaseLetter⟩ => true
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

@[inherit_doc isCasedLetter]
protected abbrev isLC := isCasedLetter

/-- Check if modifier letter character (`Lm`)

  Unicode Property: `General_Category=Lm`-/
@[inline]
def isModifierLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierLetter⟩ => true
  | _ => false

@[inherit_doc isModifierLetter]
protected abbrev isLm := isModifierLetter

/-- Check if other letter character (`Lo`)

  Unicode Property: `General_Category=Lo`-/
@[inline]
def isOtherLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherLetter⟩ => true
  | _ => false

@[inherit_doc isOtherLetter]
protected abbrev isLo := isOtherLetter

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode Property: `General_Category=M` -/
@[inline]
def isMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.mark, _⟩ => true
  | _ => false

@[inherit_doc isMark]
protected abbrev isM := isMark

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode Property: `General_Category=Mn` -/
@[inline]
def isNonspacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .nonspacingMark⟩ => true
  | _ => false

@[inherit_doc isNonspacingMark]
protected abbrev isMn := isNonspacingMark

/-- Check if spacing combining mark character (`Mc`)

  Unicode Property: `General_Category=Mc` -/
@[inline]
def isSpacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spacingMark⟩ => true
  | _ => false

@[inherit_doc isSpacingMark]
protected abbrev isMc := isSpacingMark

/-- Check if enclosing combining mark character (`Me`)

  Unicode Property: `General_Category=Me` -/
@[inline]
def isEnclosingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .enclosingMark⟩ => true
  | _ => false

@[inherit_doc isEnclosingMark]
protected abbrev isMe := isEnclosingMark

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode Property: `General_Category=N` -/
@[inline]
def isNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.number, _⟩ => true
  | _ => false

@[inherit_doc isNumber]
protected abbrev isN := isNumber

/-- Check if decimal number character (`Nd`)

  Unicode Property: `General_Category=Nd` -/
@[inline]
def isDecimalNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .decimalNumber⟩ => true
  | _ => false

@[inherit_doc isDecimalNumber]
protected abbrev isNd := isDecimalNumber

/-- Check if letter number character (`Nl`)

  Unicode Property: `General_Category=Nl` -/
@[inline]
def isLetterNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .letterNumber⟩ => true
  | _ => false

@[inherit_doc isLetterNumber]
protected abbrev isNl := isLetterNumber

/-- Check if other number character (`No`)

  Unicode Property: `General_Category=No` -/
@[inline]
def isOtherNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherNumber⟩ => true
  | _ => false

@[inherit_doc isOtherNumber]
protected abbrev isNo := isOtherNumber

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode Property: `General_Category=P` -/
@[inline]
def isPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.punctuation, _⟩ => true
  | _ => false

@[inherit_doc isPunctuation]
protected abbrev isP := isPunctuation

/-- Check if connector punctuation character (`Pc`)

  Unicode Property: `General_Category=Pc` -/
@[inline]
def isConnectorPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .connectorPunctuation⟩ => true
  | _ => false

@[inherit_doc isConnectorPunctuation]
protected abbrev isPc := isConnectorPunctuation

/-- Check if dash punctuation character (`Pd`)

  Unicode Property: `General_Category=Pd` -/
@[inline]
def isDashPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .dashPunctuation⟩ => true
  | _ => false

@[inherit_doc isDashPunctuation]
protected abbrev isPd := isDashPunctuation

/-- Check if open punctuation character (`Ps`)

  Unicode Property: `General_Category=Ps` -/
@[inline]
def isOpenPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .openPunctuation⟩ => true
  | _ => false

@[inherit_doc isOpenPunctuation]
protected abbrev isPs := isOpenPunctuation

/-- Check if close punctuation character (`Pe`)

  Unicode Property: `General_Category=Pe` -/
@[inline]
def isClosePunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .closePunctuation⟩ => true
  | _ => false

@[inherit_doc isClosePunctuation]
protected abbrev isPe := isClosePunctuation

/-- Check if initial punctuation character (`Pi`)

  Unicode Property: `General_Category=Pi` -/
@[inline]
def isInitialPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .initialPunctuation⟩ => true
  | _ => false

@[inherit_doc isInitialPunctuation]
protected abbrev isPi := isInitialPunctuation

/-- Check if initial punctuation character (`Pf`)

  Unicode Property: `General_Category=Pf` -/
@[inline]
def isFinalPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .finalPunctuation⟩ => true
  | _ => false

@[inherit_doc isFinalPunctuation]
protected abbrev isPf := isFinalPunctuation

/-- Check if other punctuation character (`Po`)

  Unicode Property: `General_Category=Po` -/
@[inline]
def isOtherPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherPunctuation⟩ => true
  | _ => false

@[inherit_doc isOtherPunctuation]
protected abbrev isPo := isOtherPunctuation

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode Property: `General_Category=S` -/
@[inline]
def isSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.symbol, _⟩ => true
  | _ => false

@[inherit_doc isSymbol]
protected abbrev isS := isSymbol

/-- Check if math symbol character (`Sm`)

  Unicode Property: `General_Category=Sm` -/
@[inline]
def isMathSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .mathSymbol⟩ => true
  | _ => false

@[inherit_doc isMathSymbol]
protected abbrev isSm := isMathSymbol

/-- Check if currency symbol character (`Sc`)

  Unicode Property: `General_Category=Sc` -/
def isCurrencySymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .currencySymbol⟩ => true
  | _ => false

@[inherit_doc isCurrencySymbol]
protected abbrev isSc := isCurrencySymbol

/-- Check if modifier symbol character (`Sk`)

  Unicode Property: `General_Category=Sk` -/
@[inline]
def isModifierSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierSymbol⟩ => true
  | _ => false

@[inherit_doc isModifierSymbol]
protected abbrev isSk := isModifierSymbol

/-- Check if other symbol character (`So`)

  Unicode Property: `General_Category=So` -/
@[inline]
def isOtherSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherSymbol⟩ => true
  | _ => false

@[inherit_doc isOtherSymbol]
protected abbrev isSo := isOtherSymbol

/-- Check if separator character (`Z`)

  This is a derived property (`Z = Zs | Zl | Zp`).

  Unicode Property: `General_Category=Z` -/
@[inline]
def isSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.separator, _⟩ => true
  | _ => false

@[inherit_doc isSeparator]
protected abbrev isZ := isSeparator

/-- Check if space separator character (`Zs`)

  Unicode Property: `General_Category=Zs` -/
@[inline]
def isSpaceSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spaceSeparator⟩ => true
  | _ => false

@[inherit_doc isSpaceSeparator]
protected abbrev isZs := isSpaceSeparator

/-- Check if line separator character (`Zl`)

  Unicode Property: `General_Category=Zl` -/
@[inline]
def isLineSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lineSeparator⟩ => true
  | _ => false

@[inherit_doc isLineSeparator]
protected abbrev isZl := isLineSeparator

/-- Check if paragraph separator character (`Zp`)

  Unicode Property: `General_Category=Zp` -/
@[inline]
def isParagraphSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .paragraphSeparator⟩ => true
  | _ => false

@[inherit_doc isParagraphSeparator]
protected abbrev isZp := isParagraphSeparator

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode Property: `General_Category=C` -/
@[inline]
def isOther (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.other, _⟩ => true
  | _ => false

@[inherit_doc isOther]
protected abbrev isC := isOther

/-- Check if control character (`Cc`)

  Unicode Property: `General_Category=Cc` -/
@[inline]
def isControl (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .control⟩ => true
  | _ => false

@[inherit_doc isControl]
protected abbrev isCc := isControl

/-- Check if format character (`Cf`)

  Unicode Property: `General_Category=Cf` -/
@[inline]
def isFormat (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .format⟩ => true
  | _ => false

@[inherit_doc isFormat]
protected abbrev isCf := isFormat

/-- Check if surrogate character (`Cs`)

  Unicode Property: `General_Category=Cs` -/
@[inline]
def isSurrogate (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .surrogate⟩ => true
  | _ => false

@[inherit_doc isSurrogate]
protected abbrev isCs := isSurrogate

/-- Check if private use character (`Co`)

  Unicode Property: `General_Category=Co` -/
@[inline]
def isPrivateUse (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .privateUse⟩ => true
  | _ => false

@[inherit_doc isPrivateUse]
protected abbrev isCo := isPrivateUse

/-- Check if unassigned character (`Cn`)

  Unicode Property: `General_Category=Cn` -/
@[inline]
def isUnassigned (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .unassigned⟩ => true
  | _ => false

@[inherit_doc isUnassigned]
protected abbrev isCn := isUnassigned

end GeneralCategory

/-!
  ## Case Type and Mapping ##
-/

/-- Map character to lowercase

  This function does not handle the case where the lowercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Lowercase_Mapping` -/
@[inline]
def getLowerChar (char : Char) : Char :=
  match lookupCaseMapping char.val with
  | (_, lc, _) => Char.ofNat lc.toNat

/-- Map character to uppercase

  This function does not handle the case where the uppercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Uppercase_Mapping` -/
@[inline]
def getUpperChar (char : Char) : Char :=
  match lookupCaseMapping char.val with
  | (uc, _, _) => Char.ofNat uc.toNat

/-- Map character to titlecase

  This function does not handle the case where the titlecase mapping would
  consist of more than one character.

  Unicode property: `Simple_Titlecase_Mapping` -/
@[inline]
def getTitleChar (char : Char) : Char :=
  match lookupCaseMapping char.val with
  | (_, _, tc) => Char.ofNat tc.toNat

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical decomposition of character (`NFD`)

  Unicode property: `Decomposition_Mapping` -/
partial def getCanonicalDecomposition (char : Char) : String :=
  /-
    In some instances a canonical mapping or a compatibility mapping may consist of a single
    character. For a canonical mapping, this indicates that the character is a canonical
    equivalent of another single character. For a compatibility mapping, this indicates that the
    character is a compatibility equivalent of another single character.

    A canonical mapping may also consist of a pair of characters, but is never longer than two
    characters. When a canonical mapping consists of a pair of characters, the first character may
    itself be a character with a decomposition mapping, but the second character never has a
    decomposition mapping.
  -/
  String.mk <| loop [char.val] |>.map fun c => Char.ofNat c.toNat
where
  loop : List UInt32 → List UInt32
  | c :: cs =>
    match lookupCanonicalDecompositionMapping c with
    | #[] => c :: cs
    | #[c] => loop (c :: cs)
    | #[c₀, c₁] => loop (c₀ :: c₁ :: cs)
    | _ => panic! "invalid canonical decomposition mapping"
  | _ => unreachable!

/-!
  ## Numeric Type and Value ##
-/

/-- Check if character represents a numerical value

  Unicode property: `Numeric_Type=Numeric` -/
@[inline]
def isNumeric (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some _ => true
    | _ => otherNumeric.elem char.val
where
  -- Extracted
  otherNumeric := #[
    0x3405, 0x3483, 0x382A, 0x3B4D, 0x4E00, 0x4E03, 0x4E07, 0x4E09, 0x4E5D, 0x4E8C,
    0x4E94, 0x4E96, 0x4EBF, 0x4EC0, 0x4EDF, 0x4EE8, 0x4F0D, 0x4F70, 0x5104, 0x5146,
    0x5169, 0x516B, 0x516D, 0x5341, 0x5343, 0x5344, 0x5345, 0x534C, 0x53C1, 0x53C2,
    0x53C3, 0x53C4, 0x56DB, 0x58F1, 0x58F9, 0x5E7A, 0x5EFE, 0x5EFF, 0x5F0C, 0x5F0D,
    0x5F0E, 0x5F10, 0x62FE, 0x634C, 0x67D2, 0x6F06, 0x7396, 0x767E, 0x8086, 0x842C,
    0x8CAE, 0x8CB3, 0x8D30, 0x9621, 0x9646, 0x964C, 0x9678, 0x96F6, 0xF96B, 0xF973,
    0xF978, 0xF9B2, 0xF9D1, 0xF9D3, 0xF9FD, 0x20001, 0x20064, 0x200E2, 0x20121, 0x2092A,
    0x20983, 0x2098C, 0x2099C, 0x20AEA, 0x20AFD, 0x20B19, 0x22390, 0x22998, 0x23B1B, 0x2626D,
    0x2F890]

/-- Check if character represents a digit in base 10

  Unicode property: `Numeric_Type=Digit` -/
@[inline]
def isDigit (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | some (.digit _) => true
    | _ => false

/-- Get value of digit

  Unicode properties: `Numeric_Value`, `Numeric_Type=Digit` -/
@[inline]
def getDigit? (char : Char) : Option (Fin 10) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char.toNat < '0'.toNat then
      none
    else
      let n := char.toNat - '0'.toNat
      if h : n < 10 then
        some ⟨n, h⟩
      else
        none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) => some value
    | some (.digit value) => some value
    | _ => none

/-- Check if character represents a decimal digit

  For this property, a character must be part of a contiguous sequence
  representing the ten decimal digits in order from 0 to 9.

  Unicode property: `Numeric_Type=Decimal` -/
@[inline]
def isDecimal (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | _ => false

/-- Get decimal digit range

  If the character is part of a contiguous sequence representing the ten
  decimal digits in order from 0 to 9, this function returns the first and
  last characters from this range.

  Unicode property: `Numeric_Type=Decimal` -/
@[inline]
def getDecimalRange? (char : Char) : Option (Char × Char) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char >= '0' && char <= '9' then
      some ('0', '9')
    else
      none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) =>
      let first := char.toNat - value.val
      some (Char.ofNat first, Char.ofNat (first + 9))
    | _ => none

/-- Check if character represents a digit in base 16

  Unicode property: `Hex_Digit` -/
@[inline]
def isHexDigit (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val <= 0x0039 && char.val >= 0x0030 || -- [10] DIGIT ZERO..DIGIT NINE
  char.val <= 0x0046 && char.val >= 0x0041 || --  [6] LATIN CAPITAL LETTER A..LATIN CAPITAL LETTER F
  char.val <= 0x0066 && char.val >= 0x0061 || --  [6] LATIN SMALL LETTER A..LATIN SMALL LETTER F
  char.val <= 0xFF19 && char.val >= 0xFF10 || -- [10] FULLWIDTH DIGIT ZERO..FULLWIDTH DIGIT NINE
  char.val <= 0xFF26 && char.val >= 0xFF21 || --  [6] FULLWIDTH LATIN CAPITAL LETTER A..FULLWIDTH LATIN CAPITAL LETTER F
  char.val <= 0xFF46 && char.val >= 0xFF41    --  [6] FULLWIDTH LATIN SMALL LETTER A..FULLWIDTH LATIN SMALL LETTER F

/-- Get value of digit

  Unicode properties: `Hex_Digit` -/
@[inline]
def getHexDigit? (char : Char) : Option (Fin 16) :=
  if char.toNat < 0x30 then
    none
  else
    let n := if char.toNat < 0xFF10 then char.toNat - 0x0030 else char.toNat - 0xFF10
    if h : n < 10 then
      some ⟨n, Nat.lt_trans h (by decide)⟩
    else if n >= 17 then
      let n := n - 7
      if h : n < 16 then
        some ⟨n, h⟩
      else if n >= 32 then
        if h : n - 32 < 16 then
          some ⟨n - 32, h⟩
        else
          none
      else
        none
    else
      none

/-!
  ## Other Properties ##
-/

/-- Check if white space character

  Unicode property: `White_Space`
-/
@[inline]
def isWhiteSpace (char : Char) : Bool :=
  if char.val < 0x100 then
    char == ' ' || char >= '\t' && char <= '\r'
      || char.val == 0x85 || char.val == 0xA0
  else
    GeneralCategory.isSeparator char

/-- Check if lowercase letter character

  Unicode property: `Lowercase` -/
@[inline]
def isLowercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'a' ≤ char && char ≤ 'z'
  else
    lookupLowercase char.val

/-- Check if uppercase letter character

  Unicode property: `Uppercase` -/
@[inline]
def isUppercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z'
  else
    lookupUppercase char.val

/-- Check if cased letter character

  Unicode property: `Cased` -/
@[inline]
def isCased (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupCased char.val

/-- Check if character is ignorable for casing purposes

  Generated from general categories `Lm`, `Mn`, `Me`, `Sk`, `Cf`, and word
  break properties `MidLetter`, `MidNumLet`, `Single_Quote`.

  Unicode property: `Case_Ignorable` -/
@[inline]
def isCaseIgnorable (char : Char) : Bool :=
  -- Extracted from `auxiliary/WordBreakProperty.txt`
  let other : List UInt32 := [
    0x0027, -- Single_Quote APOSTROPHE
    0x002E, -- MidNumLet    FULL STOP
    0x003A, -- MidLetter    COLON
    0x00B7, -- MidLetter    MIDDLE DOT
    0x0387, -- MidLetter    GREEK ANO TELEIA
    0x055F, -- MidLetter    ARMENIAN ABBREVIATION MARK
    0x05F4, -- MidLetter    HEBREW PUNCTUATION GERSHAYIM
    0x2018, -- MidNumLet    LEFT SINGLE QUOTATION MARK
    0x2019, -- MidNumLet    RIGHT SINGLE QUOTATION MARK
    0x2027, -- MidLetter    HYPHENATION POINT
    0x2024, -- MidNumLet    ONE DOT LEADER
    0xFE13, -- MidLetter    PRESENTATION FORM FOR VERTICAL COLON
    0xFE55, -- MidLetter    SMALL COLON
    0xFE52, -- MidNumLet    SMALL FULL STOP
    0xFF07, -- MidNumLet    FULLWIDTH APOSTROPHE
    0xFF0E, -- MidNumLet    FULLWIDTH FULL STOP
    0xFF1A] -- MidLetter    FULLWIDTH COLON
  match getGeneralCategory char with
  | ⟨_, some .modifierLetter⟩ => true
  | ⟨_, some .nonspacingMark⟩ => true
  | ⟨_, some .enclosingMark⟩ => true
  | ⟨_, some .modifierSymbol⟩ => true
  | ⟨_, some .format⟩ => true
  | _ => other.elem char.val

/-- Check if mathematical symbol character

  Unicode property: `Math` -/
@[inline]
def isMath (char : Char) : Bool := lookupMath char.val

/-- Check if alphabetic character

  Unicode property: `Alphabetic` -/
@[inline]
def isAlphabetic (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupAlphabetic char.val

@[inherit_doc isAlphabetic]
abbrev isAlpha := isAlphabetic

end Unicode
