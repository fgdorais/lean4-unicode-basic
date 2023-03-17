/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.Types
import UnicodeBasic.UnicodeData
import UnicodeBasic.PropList

/-!
  # General API #

  As a general rule, for a given a Unicode property `Unicode_Property`.

  * If the property is boolean valued then the implementation is called
    `Unicode.isUnicodeProperty`.

  * Otherwise, the implementation is called `Unicode.getUnicodeProperty`.

  * If the value is not of standard type (`Bool`, `Char`, `Nat`, `Int`, etc.)
    or a combination thereof (e.g. `Bool × Option Nat`) then the value type is
    defined in `UnicodeData.Types`.

  * If the input type needs disambiguation (e.g. `Char` vs `String`) the type
    name may be appended to the name as in `Unicode.isUnicodePropertyChar` or
    in `Unicode.getUnicodePropertyString`.

  * If the output type is `Option _` then the suffix `?` may be appended to
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
def getName (char : Char) : String :=
  getUnicodeData char |>.characterName

/-!
  ## Bidi Class ##
-/

/-- Get character bidirectional class

  Unicode property: `Bidi_Class` -/
def getBidiClass (char : Char) : BidiClass :=
  getUnicodeData char |>.bidiClass

/-- Check if bidirectional mirrored character

  Unicode property: `Bidi_Mirrored` -/
def isBidiMirrored (char : Char) : Bool :=
  getUnicodeData char |>.bidiMirrored

/-!
  ## General Category ##
-/

/-- Get character general category

  *Caveat*: This function never returns a derived general category. Use
  `Unicode.isInGeneralCategory` to check whether a character belongs to a
  general category (derived or not).

  Unicode property: `General_Category` -/
@[inline]
def getGeneralCategory (char : Char) : GeneralCategory :=
  getUnicodeData char |>.generalCategory

/-- Check if character belongs to the general category

  Unicode property: `General_Category` -/
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
protected abbrev iscC := isControl

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
  match getUnicodeData char |>.lowercaseMapping with
  | some char => char
  | none => char

/-- Map character to uppercase

  This function does not handle the case where the uppercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Uppercase_Mapping` -/
@[inline]
def getUpperChar (char : Char) : Char :=
  match getUnicodeData char |>.uppercaseMapping with
  | some char => char
  | none => char

/-- Map character to titlecase

  This function does not handle the case where the titlecase mapping would
  consist of more than one character.

  Unicode property: `Simple_Titlecase_Mapping` -/
@[inline]
def getTitleChar (char : Char) : Char :=
  match getUnicodeData char |>.titlecaseMapping with
  | some char => char
  | none => getUpperChar char

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
  let rec loop : List Char → List Char
  | c :: cs =>
    match getUnicodeData c |>.decompositionMapping with
    | some ⟨none, ds⟩ =>
      match ds with
      | [c] => loop (c :: cs)
      | [c₀, c₁] => loop (c₀ :: c₁ :: cs)
      | _ => panic! "invalid canonical decomposition mapping"
    | _ => c :: cs
  | _ => unreachable!
  String.mk <| loop [char]

/-!
  ## Numeric Type and Value ##
-/

/-- Check if character represents a digit in base 10

  Unicode property: `Numeric_Type=Digit` -/
def isDigit (char : Char) : Bool :=
  match getUnicodeData char |>.numeric with
  | some (.decimal _) => true
  | some (.digit _) => true
  | _ => false

/-- Get value of digit

  Unicode properties: `Numeric_Value`, `Numeric_Type=Digit` -/
def getDigit? (char : Char) : Option (Fin 10) :=
  match getUnicodeData char |>.numeric with
  | some (.decimal value) => some value
  | some (.digit value) => some value
  | _ => none

/-- Check if character represents a decimal digit

  For this property, a character must be part of a contiguous sequence
  representing the ten decimal digits in order from 0 to 9.

  Unicode property: `Numeric_Type=Decimal` -/
def isDecimal (char : Char) : Bool :=
  match getUnicodeData char |>.numeric with
  | some (.decimal _) => true
  | _ => false

/-- Get decimal digit range

  If the character is part of a contiguous sequence representing the ten
  decimal digits in order from 0 to 9, this function returns the first and
  last characters from this range.

  Unicode property: `Numeric_Type=Decimal` -/
def getDecimalRange? (char : Char) : Option (Char × Char) :=
  match getUnicodeData char |>.numeric with
  | some (.decimal value) =>
    let first := char.toNat - value.val
    some (Char.ofNat first, Char.ofNat (first + 9))
  | _ => none

/-!
  ## Other Properties ##
-/

/-- Check if white space character

  Unicode property: `White_Space`
-/
@[inline]
def isWhiteSpace (char : Char) : Bool :=
  if char.val < 256 then
    char == ' ' || char >= '\t' && char <= '\r'
      || char.val == 0x85 || char.val == 0xA0
  else
    GeneralCategory.isSeparator char

/-- Check if lowercase letter character

  Unicode property: `Lowercase` -/
def isLowercase (char : Char) : Bool :=
  GeneralCategory.isLl char || PropList.isOtherLowercase char.val

/-- Check if uppercase letter character

  Unicode property: `Uppercase` -/
def isUppercase (char : Char) : Bool :=
  GeneralCategory.isLu char || PropList.isOtherUppercase char.val

/-- Check if mathematical symbol character

  Unicode property: `Math` -/
def isMath (char : Char) : Bool :=
  GeneralCategory.isSm char || PropList.isOtherMath char.val

/-- Check if alphabetic character

  Unicode property: `Alphabetic` -/
def isAlphabetic (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.letter, _⟩ => true
  | ⟨.number, some .letterNumber⟩ => true
  | _ => PropList.isOtherLowercase char.val
      || PropList.isOtherUppercase char.val
      || PropList.isOtherAlphabetic char.val

@[inherit_doc isAlphabetic]
abbrev isAlpha := isAlphabetic

/-- Check if alphabetic or digit character

  Unicode properties: `Alphabetic`, `Numeric_Type=Digit` -/
abbrev isAlphanum (char : Char) : Bool :=
  isAlphabetic char || isDigit char

end Unicode
