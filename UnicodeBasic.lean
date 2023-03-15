/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.Basic
import UnicodeBasic.Types

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
  ## Bidirectional Category ##
-/

/-- Get character bidirectional category

  Unicode property: `Bidi_Class` -/
def bidiClass (char : Char) : BidirectionalCategory :=
  getUnicodeData char |>.bidiCategory

/-- Check if bidirectional mirrored character

  Unicode property: `Bidi_Mirrored` -/
def isBidiMirrored (char : Char) : Bool :=
  getUnicodeData char |>.bidiMirrored

/-!
  ## General Category ##
-/

/-- Get character general category

  Unicode property: `General_Category` -/
def getGeneralCategory (char : Char) : GeneralCategory :=
  getUnicodeData char |>.generalCategory

/-- Check if character belongs to the general category -/
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
def isLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.letter, _⟩ => true
  | _ => false

/-- Check if lowercase letter character (`Ll`)

  Unicode Property: `General_Category=Ll` -/
def isLowercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | _ => false

/-- Check if titlecase letter character (`Lt`)

  Unicode Property: `General_Category=Lt` -/
def isTitlecaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .titlecaseLetter⟩ => true
  | _ => false

/-- Check if uppercase letter character (`Lu`)

  Unicode Property: `General_Category=Lu` -/
def isUppercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

/-- Check if cased letter character (`LC`)

  This is a derived category (`L = Lu | Ll | Lt`).

  Unicode Property: `General_Category=LC` -/
def isCasedLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | ⟨_, some .titlecaseLetter⟩ => true
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

/-- Check if modifier letter character (`Lm`)

  Unicode Property: `General_Category=Lm`-/
def isModifierLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierLetter⟩ => true
  | _ => false

/-- Check if other letter character (`Lo`)

  Unicode Property: `General_Category=Lo`-/
def isOtherLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherLetter⟩ => true
  | _ => false

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode Property: `General_Category=M` -/
def isMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.mark, _⟩ => true
  | _ => false

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode Property: `General_Category=Mn` -/
def isNonspacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .nonspacingMark⟩ => true
  | _ => false

/-- Check if spacing combining mark character (`Mc`)

  Unicode Property: `General_Category=Mc` -/
def isSpacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spacingMark⟩ => true
  | _ => false

/-- Check if enclosing combining mark character (`Me`)

  Unicode Property: `General_Category=Me` -/
def isEnclosingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .enclosingMark⟩ => true
  | _ => false

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode Property: `General_Category=N` -/
def isNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.number, _⟩ => true
  | _ => false

/-- Check if decimal number character (`Nd`)

  Unicode Property: `General_Category=Nd` -/
def isDecimalNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .decimalNumber⟩ => true
  | _ => false

/-- Check if letter number character (`Nl`)

  Unicode Property: `General_Category=Nl` -/
def isLetterNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .letterNumber⟩ => true
  | _ => false

/-- Check if other number character (`No`)

  Unicode Property: `General_Category=No` -/
def isOtherNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherNumber⟩ => true
  | _ => false

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode Property: `General_Category=P` -/
def isPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.punctuation, _⟩ => true
  | _ => false

/-- Check if connector punctuation character (`Pc`)

  Unicode Property: `General_Category=Pc` -/
def isConnectorPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .connectorPunctuation⟩ => true
  | _ => false

/-- Check if dash punctuation character (`Pd`)

  Unicode Property: `General_Category=Pd` -/
def isDashPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .dashPunctuation⟩ => true
  | _ => false

/-- Check if open punctuation character (`Ps`)

  Unicode Property: `General_Category=Ps` -/
def isOpenPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .openPunctuation⟩ => true
  | _ => false

/-- Check if close punctuation character (`Pe`)

  Unicode Property: `General_Category=Pe` -/
def isClosePunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .closePunctuation⟩ => true
  | _ => false

/-- Check if initial punctuation character (`Pi`)

  Unicode Property: `General_Category=Pi` -/
def isInitialPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .initialPunctuation⟩ => true
  | _ => false

/-- Check if initial punctuation character (`Pf`)

  Unicode Property: `General_Category=Pf` -/
def isFinalPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .finalPunctuation⟩ => true
  | _ => false

/-- Check if other punctuation character (`Po`)

  Unicode Property: `General_Category=Po` -/
def isOtherPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherPunctuation⟩ => true
  | _ => false

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode Property: `General_Category=S` -/
def isSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.symbol, _⟩ => true
  | _ => false

/-- Check if math symbol character (`Sm`)

  Unicode Property: `General_Category=Sm` -/
def isMathSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .mathSymbol⟩ => true
  | _ => false

/-- Check if currency symbol character (`Sc`)

  Unicode Property: `General_Category=Sc` -/
def isCurrencySymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .currencySymbol⟩ => true
  | _ => false

/-- Check if modifier symbol character (`Sk`)

  Unicode Property: `General_Category=Sk` -/
def isModifierSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierSymbol⟩ => true
  | _ => false

/-- Check if other symbol character (`So`)

  Unicode Property: `General_Category=So` -/
def isOtherSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherSymbol⟩ => true
  | _ => false

/-- Check if separator character (`Z`)

  This is a derived property (`Z = Zs | Zl | Zp`).

  Unicode Property: `General_Category=Z` -/
def isSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.separator, _⟩ => true
  | _ => false

/-- Check if space separator character (`Zs`)

  Unicode Property: `General_Category=Zs` -/
def isSpaceSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spaceSeparator⟩ => true
  | _ => false

/-- Check if line separator character (`Zl`)

  Unicode Property: `General_Category=Zl` -/
def isLineSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lineSeparator⟩ => true
  | _ => false

/-- Check if paragraph separator character (`Zp`)

  Unicode Property: `General_Category=Zp` -/
def isParagraphSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .paragraphSeparator⟩ => true
  | _ => false

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode Property: `General_Category=C` -/
def isOther (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.other, _⟩ => true
  | _ => false

/-- Check if control character (`Cc`)

  Unicode Property: `General_Category=Cc` -/
def isControl (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .control⟩ => true
  | _ => false

/-- Check if format character (`Cf`)

  Unicode Property: `General_Category=Cf` -/
def isFormat (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .format⟩ => true
  | _ => false

/-- Check if surrogate character (`Cs`)

  Unicode Property: `General_Category=Cs` -/
def isSurrogate (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .surrogate⟩ => true
  | _ => false

/-- Check if private use character (`Co`)

  Unicode Property: `General_Category=Co` -/
def isPrivateUse (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .privateUse⟩ => true
  | _ => false

/-- Check if unassigned character (`Cn`)

  Unicode Property: `General_Category=Cn` -/
def isUnassigned (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .unassigned⟩ => true
  | _ => false

end GeneralCategory

/-!
  ## Case Type and Mapping ##
-/

/-- Map character to lowercase

  This function does not handle the case where the lowercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Lowercase_Mapping` -/
def toLower (char : Char) : Char :=
  match getUnicodeData char |>.lowercaseMapping with
  | some char => char
  | none => char

/-- Map character to uppercase

  This function does not handle the case where the uppercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Uppercase_Mapping` -/
def toUpper (char : Char) : Char :=
  match getUnicodeData char |>.uppercaseMapping with
  | some char => char
  | none => char

/-- Map character to titlecase

  This function does not handle the case where the titlecase mapping would
  consist of more than one character.

  Unicode property: `Simple_Titlecase_Mapping` -/
def toTitle (char : Char) : Char :=
  match getUnicodeData char |>.titlecaseMapping with
  | some char => char
  | none => toUpper char

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical decomposition of character (`NFD`)

  Unicode property: `Decomposition_Mapping` -/
partial def canonicalDecomposition (char : Char) : String :=
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
def toDigit? (char : Char) : Option (Fin 10) :=
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

/-- Get base of decimal digit range

  If the character is part of a contiguous sequence representing the ten
  decimal digits in order from 0 to 9, this function returns the character
  representing 0 from that range.

  Unicode property: `Numeric_Type=Decimal` -/
def decimalDigitZero? (char : Char) : Option Char :=
  match getUnicodeData char |>.numeric with
  | some (.decimal value) => some (Char.ofNat (char.toNat - value.val))
  | _ => none

end Unicode
