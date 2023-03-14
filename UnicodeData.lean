/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeData.Basic
import UnicodeData.Types

namespace Unicode

/-- Get character Unicode data -/
def getUnicodeData (char : Char) : UnicodeData :=
  match getUnicodeData? char.val with
  | some data => data
  | none => unreachable!

/-- Get character name -/
def getName (char : Char) : String :=
  UnicodeData.characterName <| getUnicodeData char

/-- Get character bidirectional class -/
def getBidiCategory (char : Char) : BidirectionalCategory :=
  UnicodeData.bidiCategory <| getUnicodeData char

/-- Check if bidirectional mirrored character -/
def isBidiMirrored (char : Char) : Bool :=
  UnicodeData.bidiMirrored <| getUnicodeData char

/-- Get character general category -/
def getGeneralCategory (char : Char) : GeneralCategory :=
  UnicodeData.generalCategory <| getUnicodeData char

/-- Check if character belongs to the general category -/
def isInGeneralCategory (char : Char) (category : GeneralCategory) : Bool :=
  match category, getGeneralCategory char with
  | ⟨major, none⟩, ⟨charMajor, _⟩ => major = charMajor
  | ⟨_, some .casedLetter⟩, ⟨_, some .lowercaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, ⟨_, some .titlecaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, ⟨_, some .uppercaseLetter⟩ => true
  | ⟨_, some .casedLetter⟩, _ => false
  | cat, charCat => cat = charCat

/-- Check if letter character (general category L) -/
def isLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.letter, _⟩ => true
  | _ => false

/-- Check if lowercase letter character (general category Ll) -/
def isLowercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | _ => false

/-- Check if titlecase letter character (general category Lt) -/
def isTitlecaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .titlecaseLetter⟩ => true
  | _ => false

/-- Check if uppercase letter character (general category Lu) -/
def isUppercaseLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

/-- Check if cased letter character (general category LC) -/
def isCasedLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lowercaseLetter⟩ => true
  | ⟨_, some .titlecaseLetter⟩ => true
  | ⟨_, some .uppercaseLetter⟩ => true
  | _ => false

/-- Check if modifier letter character (general category Lm)-/
def isModifierLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierLetter⟩ => true
  | _ => false

/-- Check if other letter character (general category Lo)-/
def isOtherLetter (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherLetter⟩ => true
  | _ => false

/-- Check if mark character (general category M) -/
def isMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.mark, _⟩ => true
  | _ => false

/-- Check if nonspacing mark character (general category Mn) -/
def isNonspacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .nonspacingMark⟩ => true
  | _ => false

/-- Check if nonspacing mark character (general category Mc) -/
def isSpacingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spacingMark⟩ => true
  | _ => false

/-- Check if enclosing mark character (general category Me) -/
def isEnclosingMark (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .enclosingMark⟩ => true
  | _ => false

/-- Check if number character (general category N) -/
def isNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.number, _⟩ => true
  | _ => false

/-- Check if decimal number character (general category Nd) -/
def isDecimalNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .decimalNumber⟩ => true
  | _ => false

/-- Check if letter number character (general category Nl) -/
def isLetterNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .letterNumber⟩ => true
  | _ => false

/-- Check if other number character (general category No) -/
def isOtherNumber (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherNumber⟩ => true
  | _ => false

/-- Check if punctuation character (general category P) -/
def isPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.punctuation, _⟩ => true
  | _ => false

/-- Check if connector punctuation character (general category Pc) -/
def isConnectorPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .connectorPunctuation⟩ => true
  | _ => false

/-- Check if dash punctuation character (general category Pd) -/
def isDashPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .dashPunctuation⟩ => true
  | _ => false

/-- Check if open punctuation character (general category Ps) -/
def isOpenPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .openPunctuation⟩ => true
  | _ => false

/-- Check if close punctuation character (general category Pe) -/
def isClosePunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .closePunctuation⟩ => true
  | _ => false

/-- Check if initial punctuation character (general category Pi) -/
def isInitialPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .initialPunctuation⟩ => true
  | _ => false

/-- Check if initial punctuation character (general category Pf) -/
def isFinalPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .finalPunctuation⟩ => true
  | _ => false

/-- Check if other punctuation character (general category Po) -/
def isOtherPunctuation (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherPunctuation⟩ => true
  | _ => false

/-- Check if symbol character (general category S) -/
def isSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.symbol, _⟩ => true
  | _ => false

/-- Check if math symbol character (general category Sm) -/
def isMathSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .mathSymbol⟩ => true
  | _ => false

/-- Check if currency symbol character (general category Sc) -/
def isCurrencySymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .currencySymbol⟩ => true
  | _ => false

/-- Check if modifier symbol character (general category Sk) -/
def isModifierSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .modifierSymbol⟩ => true
  | _ => false

/-- Check if other symbol character (general category So) -/
def isOtherSymbol (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .otherSymbol⟩ => true
  | _ => false

/-- Check if separator character (general category Z) -/
def isSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.separator, _⟩ => true
  | _ => false

/-- Check if space separator character (general category Zs) -/
def isSpaceSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .spaceSeparator⟩ => true
  | _ => false

/-- Check if line separator character (general category Zl) -/
def isLineSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .lineSeparator⟩ => true
  | _ => false

/-- Check if paragraph separator character (general category Zp) -/
def isParagraphSeparator (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .paragraphSeparator⟩ => true
  | _ => false

/-- Check if other character (general category C) -/
def isOther (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨.other, _⟩ => true
  | _ => false

/-- Check if control character (general category Cc) -/
def isControl (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .control⟩ => true
  | _ => false

/-- Check if format character (general category Cf) -/
def isFormat (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .format⟩ => true
  | _ => false

/-- Check if surrogate character (general category Cs) -/
def isSurrogate (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .surrogate⟩ => true
  | _ => false

/-- Check if private use character (general category Co) -/
def isPrivateUse (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .privateUse⟩ => true
  | _ => false

/-- Check if unassigned character (general category Cn) -/
def isUnassigned (char : Char) : Bool :=
  match getGeneralCategory char with
  | ⟨_, some .unassigned⟩ => true
  | _ => false

/-- Convert character to lowercase -/
def toLower (char : Char) : Char :=
  match UnicodeData.lowercaseMapping <| getUnicodeData char with
  | some char => char
  | none => char

/-- Convert character to uppercase -/
def toUpper (char : Char) : Char :=
  match UnicodeData.uppercaseMapping <| getUnicodeData char with
  | some char => char
  | none => char

/-- Convert character to titlecase -/
def toTitle (char : Char) : Char :=
  match UnicodeData.titlecaseMapping <| getUnicodeData char with
  | some char => char
  | none => toUpper char

/-- Canonical decomposition of character (NFD) -/
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
    match UnicodeData.decompositionMapping <| getUnicodeData c with
    | some ⟨none, ds⟩ =>
      match ds with
      | [c] => loop (c :: cs)
      | [c₀, c₁] => loop (c₀ :: c₁ :: cs)
      | _ => panic! "invalid canonical decomposition mapping"
    | _ => c :: cs
  | _ => unreachable!
  String.mk <| loop [char]

/-- Check if character represents a decimal digit -/
def isDigit (char : Char) : Bool :=
  match UnicodeData.numeric <| getUnicodeData char with
  | some (.decimal _) => true
  | some (.digit _) => true
  | _ => false

/-- Get value of decimal digit -/
def toDigit? (char : Char) : Option (Fin 10) :=
  match UnicodeData.numeric <| getUnicodeData char with
  | some (.decimal value) => some value
  | some (.digit value) => some value
  | _ => none

/-- Check if character is part of a contiguous sequence representing decimal digits 0 .. 9 -/
def isDecimal (char : Char) : Bool :=
  match UnicodeData.numeric <| getUnicodeData char with
  | some (.decimal _) => true
  | _ => false

/-- If the character is part of a contiguous sequence representing decimal digits 0 .. 9,
  then get the zero digit from that sequence -/
def decimalDigitZero? (char : Char) : Option Char :=
  match UnicodeData.numeric <| getUnicodeData char with
  | some (.decimal value) => some (Char.ofNat (char.toNat - value.val))
  | _ => none

end Unicode
