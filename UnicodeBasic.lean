/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
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

  Unicode general categories are encoded using the type `GC`. This type has
  a boolean algebra structure with inclusion `⊆`, meet/intersection `&&&`,
  join/union `|||` and complement `~~~`. The relation `∈` is provided to
  check whether a character belongs to a given category. For example,
  `c ∈ (GC.L &&& ~~~GC.Lt) ||| GC.Z` checks whether `c` is a either a
  non-titlecase letter or a separator.
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
def getGC (char : Char) : GC :=
  -- ASCII shortcut
  if h : char.toNat < table.size then
    table[char.toNat]
  else
    lookupGC char.val
where
  table : Array GC :=
    #[.Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Zs, .Po, .Po, .Po, .Sc, .Po, .Po, .Po, .Ps, .Po, .Po, .Sm, .Po, .Pd, .Po, .Po,
      .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Po, .Po, .Sm, .Sm, .Sm, .Po,
      .Po, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu,
      .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Ps, .Po, .Po, .Sk, .Pc,
      .Sk, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll,
      .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ps, .Sm, .Po, .Sm, .Cc]

instance : Membership Char GC where
  mem cat char := getGC char ⊆ cat

instance (char : Char) (cat : GC) : Decidable (char ∈ cat) := inferInstanceAs (Decidable (_ ⊆ _))


namespace GeneralCategory

/-- Check if letter character (`L`)

  This is a derived category (`L = Lu | Ll | Lt | Lm | Lo`).

  Unicode Property: `General_Category=L` -/
abbrev isLetter (char : Char) : Bool := char ∈ Unicode.GC.L

/-- Check if lowercase letter character (`Ll`)

  Unicode Property: `General_Category=Ll` -/
abbrev isLowercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Ll

/-- Check if titlecase letter character (`Lt`)

  Unicode Property: `General_Category=Lt` -/
abbrev isTitlecaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lt

/-- Check if uppercase letter character (`Lu`)

  Unicode Property: `General_Category=Lu` -/
abbrev isUppercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lu

/-- Check if cased letter character (`LC`)

  This is a derived category (`L = Lu | Ll | Lt`).

  Unicode Property: `General_Category=LC` -/
abbrev isCasedLetter (char : Char) : Bool := char ∈ Unicode.GC.LC

/-- Check if modifier letter character (`Lm`)

  Unicode Property: `General_Category=Lm`-/
abbrev isModifierLetter (char : Char) : Bool := char ∈ Unicode.GC.Lm

/-- Check if other letter character (`Lo`)

  Unicode Property: `General_Category=Lo`-/
abbrev isOtherLetter (char : Char) : Bool := char ∈ Unicode.GC.Lo

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode Property: `General_Category=M` -/
abbrev isMark (char : Char) : Bool := char ∈ Unicode.GC.M

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode Property: `General_Category=Mn` -/
abbrev isNonspacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mn

/-- Check if spacing combining mark character (`Mc`)

  Unicode Property: `General_Category=Mc` -/
abbrev isSpacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mc

/-- Check if enclosing combining mark character (`Me`)

  Unicode Property: `General_Category=Me` -/
abbrev isEnclosingMark (char : Char) : Bool := char ∈ Unicode.GC.Me

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode Property: `General_Category=N` -/
abbrev isNumber (char : Char) : Bool := char ∈ Unicode.GC.N

/-- Check if decimal number character (`Nd`)

  Unicode Property: `General_Category=Nd` -/
abbrev isDecimalNumber (char : Char) : Bool := char ∈ Unicode.GC.Nd

/-- Check if letter number character (`Nl`)

  Unicode Property: `General_Category=Nl` -/
abbrev isLetterNumber (char : Char) : Bool := char ∈ Unicode.GC.Nl

/-- Check if other number character (`No`)

  Unicode Property: `General_Category=No` -/
abbrev isOtherNumber (char : Char) : Bool := char ∈ Unicode.GC.No

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode Property: `General_Category=P` -/
abbrev isPunctuation (char : Char) : Bool := char ∈ Unicode.GC.P

/-- Check if connector punctuation character (`Pc`)

  Unicode Property: `General_Category=Pc` -/
abbrev isConnectorPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pc

/-- Check if dash punctuation character (`Pd`)

  Unicode Property: `General_Category=Pd` -/
abbrev isDashPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pd

/-- Check if grouping punctuation character (`PG`)

  This is a derived category (`PG = Ps | Pe`).

  Unicode Property: `General_Category=PG` -/
abbrev isGroupPunctuation (char : Char) : Bool := char ∈ Unicode.GC.PG

/-- Check if open punctuation character (`Ps`)

  Unicode Property: `General_Category=Ps` -/
abbrev isOpenPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Ps

/-- Check if close punctuation character (`Pe`)

  Unicode Property: `General_Category=Pe` -/
abbrev isClosePunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pe

/-- Check if quoting punctuation character (`PQ`)

  This is a derived category (`PQ = Pi | Pf`).

  Unicode Property: `General_Category=PQ` -/
abbrev isQuotePunctuation (char : Char) : Bool := char ∈ Unicode.GC.PQ

/-- Check if initial punctuation character (`Pi`)

  Unicode Property: `General_Category=Pi` -/
abbrev isInitialPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pi

/-- Check if initial punctuation character (`Pf`)

  Unicode Property: `General_Category=Pf` -/
abbrev isFinalPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pf

/-- Check if other punctuation character (`Po`)

  Unicode Property: `General_Category=Po` -/
abbrev isOtherPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Po

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode Property: `General_Category=S` -/
abbrev isSymbol (char : Char) : Bool := char ∈ Unicode.GC.S

/-- Check if math symbol character (`Sm`)

  Unicode Property: `General_Category=Sm` -/
abbrev isMathSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sm

/-- Check if currency symbol character (`Sc`)

  Unicode Property: `General_Category=Sc` -/
abbrev isCurrencySymbol (char : Char) : Bool := char ∈ Unicode.GC.Sc

/-- Check if modifier symbol character (`Sk`)

  Unicode Property: `General_Category=Sk` -/
abbrev isModifierSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sk

/-- Check if other symbol character (`So`)

  Unicode Property: `General_Category=So` -/
abbrev isOtherSymbol (char : Char) : Bool := char ∈ Unicode.GC.So

/-- Check if separator character (`Z`)

  This is a derived property (`Z = Zs | Zl | Zp`).

  Unicode Property: `General_Category=Z` -/
abbrev isSeparator (char : Char) : Bool := char ∈ Unicode.GC.Z

/-- Check if space separator character (`Zs`)

  Unicode Property: `General_Category=Zs` -/
abbrev isSpaceSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zs

/-- Check if line separator character (`Zl`)

  Unicode Property: `General_Category=Zl` -/
abbrev isLineSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zl

/-- Check if paragraph separator character (`Zp`)

  Unicode Property: `General_Category=Zp` -/
abbrev isParagraphSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zp

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode Property: `General_Category=C` -/
abbrev isOther (char : Char) : Bool := char ∈ Unicode.GC.C

/-- Check if control character (`Cc`)

  Unicode Property: `General_Category=Cc` -/
abbrev isControl (char : Char) : Bool := char ∈ Unicode.GC.Cc

/-- Check if format character (`Cf`)

  Unicode Property: `General_Category=Cf` -/
abbrev isFormat (char : Char) : Bool := char ∈ Unicode.GC.Cf

/-- Check if surrogate character (`Cs`)

  Does not actually occur since Lean does not regard surrogate code points as characters.

  Unicode Property: `General_Category=Cs` -/
abbrev isSurrogate (char : Char) : Bool := char ∈ Unicode.GC.Cs

/-- Check if private use character (`Co`)

  Unicode Property: `General_Category=Co` -/
abbrev isPrivateUse (char : Char) : Bool := char ∈ Unicode.GC.Co

/-- Check if unassigned character (`Cn`)

  Unicode Property: `General_Category=Cn` -/
abbrev isUnassigned (char : Char) : Bool := char ∈ Unicode.GC.Cn

end GeneralCategory

/-!
  ## Case Type and Mapping ##
-/

/-- Check if lowercase letter character

  Generated by `General_Category=Ll | Other_Lowercase`.

  Unicode property: `Lowercase` -/
@[inline]
def isLowercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'a' ≤ char && char ≤ 'z'
  else
    lookupLowercase char.val

/-- Check if uppercase letter character

  Generated by `General_Category=Lu | Other_Uppercase`.

  Unicode property: `Uppercase` -/
@[inline]
def isUppercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z'
  else
    lookupUppercase char.val

/-- Check if cased letter character

  Generated by `General_Category=LC | Other_Lowercase | Other_Uppercase`.

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
  char ∈ Unicode.GC.Lm ||| GC.Mn ||| GC.Sk ||| GC.Cf || other.elem char.val
where
  /-- Auxiliary data for `isCaseIgnorable`

    Extracted from UCD `auxiliary/WordBreakProperty.txt`. -/
  other : List UInt32 := [
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

/-- Map character to lowercase

  This function does not handle the case where the lowercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Lowercase_Mapping` -/
@[inline]
def getLowerChar (char : Char) : Char :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if 'A' ≤ char && char ≤ 'Z' then
      Char.ofNat (char.val + 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (_, lc, _) => Char.ofNat lc.toNat

/-- Map character to uppercase

  This function does not handle the case where the uppercase mapping would
  consist of more than one character.

  Unicode property: `Simple_Uppercase_Mapping` -/
@[inline]
def getUpperChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (uc, _, _) => Char.ofNat uc.toNat

/-- Map character to titlecase

  This function does not handle the case where the titlecase mapping would
  consist of more than one character.

  Unicode property: `Simple_Titlecase_Mapping` -/
@[inline]
def getTitleChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (_, _, tc) => Char.ofNat tc.toNat

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical combining class of character

  Unicode property: `Canonical_Combining_Class`
-/
def getCanonicalCombiningClass (char : Char) : Nat :=
  -- ASCII shortcut
  if char.val < 0x80 then
    0
  else
    lookupCanonicalCombiningClass char.val

/-- Get canonical decomposition of character (`NFD`)

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
def getCanonicalDecomposition (char : Char) : String :=
  -- ASCII shortcut
  if char.val < 0x80 then char.toString else
    String.ofList <| (lookupCanonicalDecompositionMapping char.val).map fun c => Char.ofNat c.toNat

/-- Get decomposition mapping of a character

  This is used in normalization to canonical decomposition (`NFD`) and compatibility
  decomposition (`NFKD`).

  Unicode properties:
  `Decomposition_Type`
  `Decomposition_Mapping` -/
def getDecompositionMapping? (char : Char) : Option DecompositionMapping :=
  -- ASCII shortcut
  if char.val < 0x80 then
    none
  else
    lookupDecompositionMapping? char.val

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

  Unicode properties:
    `Numeric_Type=Digit`
    `Numeric_Value` -/
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

  Unicode properties:
    `Numeric_Type=Decimal`
    `Numeric_Value` -/
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

/-- Check if character represents a hexadecimal digit

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

/-- Get value of a hexadecimal digit

  Unicode property: `Hex_Digit` -/
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
  -- ASCII shortcut
  if char.val < 0x80 then
    char == ' ' || char >= '\t' && char <= '\r'
  else
    GeneralCategory.isSeparator char

/-- Check if mathematical symbol character

  Generated by `GeneralCategory=Sm | Other_Math`.

  Unicode property: `Math` -/
@[inline]
def isMath (char : Char) : Bool := lookupMath char.val

/-- Check if alphabetic character

  Generated by `GeneralCategory=L | GeneralCategory=Nl | Other_Alphabetic`.

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
