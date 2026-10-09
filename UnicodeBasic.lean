/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types
public import UnicodeBasic.TableLookup

/-!
  # General API #

  As a general rule, for a given Unicode property called `Unicode_Property`,
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
    function with the suffix `!` may be implemented. This function performs
    the same calculation as the original but assumes that the input is in the
    domain; it may panic if this is not the case.

  ## General Categories ##

  Unicode general categories are encoded using the type `GC`. This type has
  a boolean algebra structure with inclusion `⊆`, meet/intersection `&&&`,
  join/union `|||` and complement `~~~`. The relation `∈` is provided to
  check whether a character belongs to a given category. For example,
  `c ∈ (GC.L &&& ~~~GC.Lt) ||| GC.Z` checks whether `c` is either a
  non-titlecase letter or a separator.

  The namespace `Unicode.GeneralCategory` provides a predicate for each
  general category, for example `GeneralCategory.isLetter` for `GC.L` and
  `GeneralCategory.isMathSymbol` for `GC.Sm`.

  ## Scripts ##

  Scripts are identified by their four-letter ISO 15924 codes using the type
  `Script`, for example `Script.ofAbbrev! "Latn"`. The function `getScript`
  returns the script of a character and `getScriptName?` returns the long
  name of a script, such as `"Latin"`. The function `getScriptSet` returns the
  `ScriptSet` of scripts a character is commonly used with; use `∈` to check
  membership, as in `Script.ofAbbrev! "Grek" ∈ getScriptSet c`.
-/

namespace Unicode

/-!
  ## Name ##
-/

/-- Get character name

  When the Unicode property `Name` is empty, a unique code point label is
  returned as recommended in Unicode Standard, section 4.8, for example
  `<control-0009>` or `<private-use-E000>`. These labels start with `'<'`
  (U+003C) and end with `'>'` (U+003E) so they are distinguishable from
  actual name values.

  Unicode property: `Name`
-/
@[inline]
public def getName (char : Char) : String := lookupName char.val

/-!
  ## Script ##
-/

/-- Get character script

  Returns `Zzzz` (Unknown) for unassigned, private use and noncharacter code
  points.

  Unicode property: `Script`
-/
@[inline]
public def getScript (char : Char) : Script := lookupScript char.val

/-- Get script name

  Returns the long name of the script, for example `"Latin"` for `Latn`.
  Returns `none` if the script code is not assigned to a script.

  Unicode property: `Script`
-/
@[inline]
public def getScriptName? (s : Script) : Option String :=
  lookupScriptName s

/-- Get the set of scripts a character is commonly used with

  If Unicode lists no such set for the character, this contains only `getScript char`.

  Note: despite its name, the `Script_Extensions` property does not extend the `Script`
  property. A set contains either one implicit script (`Zyyy` or `Zinh`) or one or more
  explicit scripts ([UAX #24, Section 3.1](https://www.unicode.org/reports/tr24/#Script_Extensions_Def)).
  So a character whose script is `Zyyy` (Common) or `Zinh` (Inherited) may get a set that
  excludes its script: U+00B7 MIDDLE DOT has script `Zyyy`, but its set is `Avst Cari Copt …`.

  Unicode property: `Script_Extensions`
-/
@[inline]
public def getScriptSet (char : Char) : ScriptSet := lookupScriptSet char.val

/-!
  ## Bidirectional Properties ##
-/

/-- Get character bidirectional class

  Unicode property: `Bidi_Class` -/
@[inline]
public def getBidiClass (char : Char) : BidiClass := lookupBidiClass char.val

/-- Check if bidirectional mirrored character

  Unicode property: `Bidi_Mirrored` -/
@[inline]
public def isBidiMirrored (char : Char) : Bool := lookupBidiMirrored char.val

/-- Check if bidirectional control character

  Unicode property: `Bidi_Control` -/
@[inline]
public def isBidiControl (char : Char) : Bool :=
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
  `char ∈ cat` to check whether a character belongs to a general category
  `cat` (derived or not).

  Unicode property: `General_Category` -/
@[inline]
public def getGC (char : Char) : GC :=
  -- ASCII shortcut
  if h : char.toNat < table.size then
    table[char.toNat]
  else
    lookupGC char.val
where
  table : Array GC :=
    #[.Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc, .Cc,
      .Zs, .Po, .Po, .Po, .Sc, .Po, .Po, .Po, .Ps, .Pe, .Po, .Sm, .Po, .Pd, .Po, .Po,
      .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Po, .Po, .Sm, .Sm, .Sm, .Po,
      .Po, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu,
      .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Ps, .Po, .Pe, .Sk, .Pc,
      .Sk, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll,
      .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ps, .Sm, .Pe, .Sm, .Cc]

/-- `char ∈ cat` holds when the general category of `char` is included in `cat` -/
public instance : Membership Char GC where
  mem cat char := getGC char ⊆ cat

public instance (char : Char) (cat : GC) : Decidable (char ∈ cat) := inferInstanceAs (Decidable (_ ⊆ _))

namespace GeneralCategory

/-- Check if letter character (`L`)

  This is a derived category (`L = Lu | Ll | Lt | Lm | Lo`).

  Unicode property: `General_Category=L` -/
public abbrev isLetter (char : Char) : Bool := char ∈ Unicode.GC.L

/-- Check if lowercase letter character (`Ll`)

  Unicode property: `General_Category=Ll` -/
public abbrev isLowercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Ll

/-- Check if titlecase letter character (`Lt`)

  Unicode property: `General_Category=Lt` -/
public abbrev isTitlecaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lt

/-- Check if uppercase letter character (`Lu`)

  Unicode property: `General_Category=Lu` -/
public abbrev isUppercaseLetter (char : Char) : Bool := char ∈ Unicode.GC.Lu

/-- Check if cased letter character (`LC`)

  This is a derived category (`LC = Lu | Ll | Lt`).

  Unicode property: `General_Category=LC` -/
public abbrev isCasedLetter (char : Char) : Bool := char ∈ Unicode.GC.LC

/-- Check if modifier letter character (`Lm`)

  Unicode property: `General_Category=Lm` -/
public abbrev isModifierLetter (char : Char) : Bool := char ∈ Unicode.GC.Lm

/-- Check if other letter character (`Lo`)

  Unicode property: `General_Category=Lo` -/
public abbrev isOtherLetter (char : Char) : Bool := char ∈ Unicode.GC.Lo

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode property: `General_Category=M` -/
public abbrev isMark (char : Char) : Bool := char ∈ Unicode.GC.M

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode property: `General_Category=Mn` -/
public abbrev isNonspacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mn

/-- Check if spacing combining mark character (`Mc`)

  Unicode property: `General_Category=Mc` -/
public abbrev isSpacingMark (char : Char) : Bool := char ∈ Unicode.GC.Mc

/-- Check if enclosing combining mark character (`Me`)

  Unicode property: `General_Category=Me` -/
public abbrev isEnclosingMark (char : Char) : Bool := char ∈ Unicode.GC.Me

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode property: `General_Category=N` -/
public abbrev isNumber (char : Char) : Bool := char ∈ Unicode.GC.N

/-- Check if decimal number character (`Nd`)

  Unicode property: `General_Category=Nd` -/
public abbrev isDecimalNumber (char : Char) : Bool := char ∈ Unicode.GC.Nd

/-- Check if letter number character (`Nl`)

  Unicode property: `General_Category=Nl` -/
public abbrev isLetterNumber (char : Char) : Bool := char ∈ Unicode.GC.Nl

/-- Check if other number character (`No`)

  Unicode property: `General_Category=No` -/
public abbrev isOtherNumber (char : Char) : Bool := char ∈ Unicode.GC.No

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode property: `General_Category=P` -/
public abbrev isPunctuation (char : Char) : Bool := char ∈ Unicode.GC.P

/-- Check if connector punctuation character (`Pc`)

  Unicode property: `General_Category=Pc` -/
public abbrev isConnectorPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pc

/-- Check if dash punctuation character (`Pd`)

  Unicode property: `General_Category=Pd` -/
public abbrev isDashPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pd

/-- Check if grouping punctuation character (`PG`)

  This is a derived category (`PG = Ps | Pe`). It is not defined by Unicode
  but is provided for convenience.

  Unicode property: `General_Category=PG` -/
public abbrev isGroupPunctuation (char : Char) : Bool := char ∈ Unicode.GC.PG

/-- Check if open punctuation character (`Ps`)

  Unicode property: `General_Category=Ps` -/
public abbrev isOpenPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Ps

/-- Check if close punctuation character (`Pe`)

  Unicode property: `General_Category=Pe` -/
public abbrev isClosePunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pe

/-- Check if quoting punctuation character (`PQ`)

  This is a derived category (`PQ = Pi | Pf`). It is not defined by Unicode
  but is provided for convenience.

  Unicode property: `General_Category=PQ` -/
public abbrev isQuotePunctuation (char : Char) : Bool := char ∈ Unicode.GC.PQ

/-- Check if initial punctuation character (`Pi`)

  Unicode property: `General_Category=Pi` -/
public abbrev isInitialPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pi

/-- Check if final punctuation character (`Pf`)

  Unicode property: `General_Category=Pf` -/
public abbrev isFinalPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Pf

/-- Check if other punctuation character (`Po`)

  Unicode property: `General_Category=Po` -/
public abbrev isOtherPunctuation (char : Char) : Bool := char ∈ Unicode.GC.Po

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode property: `General_Category=S` -/
public abbrev isSymbol (char : Char) : Bool := char ∈ Unicode.GC.S

/-- Check if math symbol character (`Sm`)

  Unicode property: `General_Category=Sm` -/
public abbrev isMathSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sm

/-- Check if currency symbol character (`Sc`)

  Unicode property: `General_Category=Sc` -/
public abbrev isCurrencySymbol (char : Char) : Bool := char ∈ Unicode.GC.Sc

/-- Check if modifier symbol character (`Sk`)

  Unicode property: `General_Category=Sk` -/
public abbrev isModifierSymbol (char : Char) : Bool := char ∈ Unicode.GC.Sk

/-- Check if other symbol character (`So`)

  Unicode property: `General_Category=So` -/
public abbrev isOtherSymbol (char : Char) : Bool := char ∈ Unicode.GC.So

/-- Check if separator character (`Z`)

  This is a derived category (`Z = Zs | Zl | Zp`).

  Unicode property: `General_Category=Z` -/
public abbrev isSeparator (char : Char) : Bool := char ∈ Unicode.GC.Z

/-- Check if space separator character (`Zs`)

  Unicode property: `General_Category=Zs` -/
public abbrev isSpaceSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zs

/-- Check if line separator character (`Zl`)

  Unicode property: `General_Category=Zl` -/
public abbrev isLineSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zl

/-- Check if paragraph separator character (`Zp`)

  Unicode property: `General_Category=Zp` -/
public abbrev isParagraphSeparator (char : Char) : Bool := char ∈ Unicode.GC.Zp

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode property: `General_Category=C` -/
public abbrev isOther (char : Char) : Bool := char ∈ Unicode.GC.C

/-- Check if control character (`Cc`)

  Unicode property: `General_Category=Cc` -/
public abbrev isControl (char : Char) : Bool := char ∈ Unicode.GC.Cc

/-- Check if format character (`Cf`)

  Unicode property: `General_Category=Cf` -/
public abbrev isFormat (char : Char) : Bool := char ∈ Unicode.GC.Cf

/-- Check if surrogate character (`Cs`)

  Does not actually occur since Lean does not regard surrogate code points as characters.

  Unicode property: `General_Category=Cs` -/
public abbrev isSurrogate (char : Char) : Bool := char ∈ Unicode.GC.Cs

/-- Check if private use character (`Co`)

  Unicode property: `General_Category=Co` -/
public abbrev isPrivateUse (char : Char) : Bool := char ∈ Unicode.GC.Co

/-- Check if unassigned character (`Cn`)

  Unicode property: `General_Category=Cn` -/
public abbrev isUnassigned (char : Char) : Bool := char ∈ Unicode.GC.Cn

end GeneralCategory

/-!
  ## Case Type and Mapping ##
-/

/-- Check if lowercase character

  This includes some characters that are not letters, such as U+24D0 CIRCLED
  LATIN SMALL LETTER A.

  Generated by `General_Category=Ll | Other_Lowercase`.

  Unicode property: `Lowercase` -/
@[inline]
public def isLowercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'a' ≤ char && char ≤ 'z'
  else
    lookupLowercase char.val

/-- Check if uppercase character

  This includes some characters that are not letters, such as U+24B6 CIRCLED
  LATIN CAPITAL LETTER A.

  Generated by `General_Category=Lu | Other_Uppercase`.

  Unicode property: `Uppercase` -/
@[inline]
public def isUppercase (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z'
  else
    lookupUppercase char.val

/-- Check if cased character

  This includes some characters that are not letters, such as U+24B6 CIRCLED
  LATIN CAPITAL LETTER A.

  Generated by `General_Category=LC | Other_Lowercase | Other_Uppercase`.

  Unicode property: `Cased` -/
@[inline]
public def isCased (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupCased char.val

/-- Check if character is ignorable for casing purposes

  Generated from general categories `Lm`, `Mn`, `Me`, `Sk`, `Cf`, and word
  break property values `MidLetter`, `MidNumLet`, `Single_Quote`.

  Unicode property: `Case_Ignorable` -/
@[inline]
public def isCaseIgnorable (char : Char) : Bool :=
  char ∈ Unicode.GC.Lm ||| GC.Mn ||| GC.Me ||| GC.Sk ||| GC.Cf || other.elem char.val
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

  Returns the character itself if it has no lowercase mapping. This function
  does not handle the case where the full lowercase mapping would consist of
  more than one character, for example U+0130 LATIN CAPITAL LETTER I WITH DOT ABOVE.

  Unicode property: `Simple_Lowercase_Mapping` -/
@[inline]
public def getLowerChar (char : Char) : Char :=
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

  Returns the character itself if it has no uppercase mapping. This function
  does not handle the case where the full uppercase mapping would consist of
  more than one character, for example U+00DF LATIN SMALL LETTER SHARP S.

  Unicode property: `Simple_Uppercase_Mapping` -/
@[inline]
public def getUpperChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (uc, _, _) => Char.ofNat uc.toNat

/-- Map character to titlecase

  Returns the character itself if it has no titlecase mapping. This function
  does not handle the case where the full titlecase mapping would consist of
  more than one character, for example U+00DF LATIN SMALL LETTER SHARP S.

  Unicode property: `Simple_Titlecase_Mapping` -/
@[inline]
public def getTitleChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'a' ≤ char && char ≤ 'z' then
      Char.ofNat (char.val - 0x20).toNat
    else
      char
  else
    match lookupCaseMapping char.val with
    | (_, _, tc) => Char.ofNat tc.toNat

/-- Simple case folding of a character

  Returns the character itself if it has no case folding. This function does
  not handle the case where case folding would consist of more than one
  character; use `getCaseFolding` for full case folding.

  Unicode property: `Simple_Case_Folding` -/
@[inline]
public def getCaseFoldingChar (char : Char) : Char :=
  if char.val < 0x80 then
    if 'A' ≤ char && char ≤ 'Z' then
      Char.ofNat (char.val + 0x20).toNat
    else
      char
  else
    match lookupCaseFolding char.val with
    | (some s, _) => Char.ofNat s.toNat
    | (none, _) => char

/-- Full case folding of a character

  The result may consist of more than one character, for example `"ss"` for
  U+00DF LATIN SMALL LETTER SHARP S.

  Unicode property: `Case_Folding` -/
@[inline]
public def getCaseFolding (char : Char) : String :=
  if char.val < 0x80 then
    if 'A' ≤ char && char ≤ 'Z' then
      Char.ofNat (char.val + 0x20).toNat |>.toString
    else
      char.toString
  else
    match lookupCaseFolding char.val with
    | (_, f@(_ :: _)) => f.foldl (fun s v => s.push (Char.ofNat v.toNat)) ""
    | (some s, []) => (Char.ofNat s.toNat).toString
    | (none, []) => char.toString

/-- Full case folding of a character as its first code point and the rest -/
@[inline]
private def unconsCaseFolding (char : Char) : UInt32 × List UInt32 :=
  if char.val < 0x80 then
    if 'A' ≤ char && char ≤ 'Z' then
      (char.val + 0x20, [])
    else
      (char.val, [])
  else
    match lookupCaseFolding char.val with
    | (_, v :: f) => (v, f)
    | (some s, []) => (s, [])
    | (none, []) => (char.val, [])

/-- Full case folding of a character, in continuation-passing style

  Calls `k` with the first character of the full case folding of `char` and
  the list of its remaining characters. For example, for U+00DF LATIN SMALL
  LETTER SHARP S, `k` is called with `'s'` and `['s']`.

  Unicode property: `Case_Folding` -/
@[inline]
public def withCaseFolding (char : Char) (k : Char → List Char → β) : β :=
  match unconsCaseFolding char with
  | (v, f) => k (Char.ofNat v.toNat) (f.map fun v => Char.ofNat v.toNat)

/-- Case-insensitive prefix match

  If `pat` matches a prefix of `s` up to full case folding, returns that prefix
  and the rest of `s`. Otherwise, returns `none`. For example, `"straße"`
  matches `"STRASSE"`, but `"ß"` does not match `"S"`, since the full case
  folding of `"ß"` is `"ss"`.

  This is default caseless matching, as defined in the Unicode Standard; it
  does not normalize either string.

  Unicode property: `Case_Folding` -/
public def matchPrefixCaseInsensitive? (pat s : String.Slice) :
    Option (String.Slice × String.Slice) :=
  loop s.startPos pat.startPos [] []
where
  loop (i : s.Pos) (j : pat.Pos) :
      List UInt32 → List UInt32 → Option (String.Slice × String.Slice)
    | a :: as, b :: bs => if a == b then loop i j as bs else none
    | [], [] =>
      if hj : j = pat.endPos then
        some (s.sliceTo i, s.sliceFrom i)
      else if hi : i = s.endPos then
        none
      else
        match unconsCaseFolding (i.get hi), unconsCaseFolding (j.get hj) with
        | (a, as), (b, bs) => if a == b then loop (i.next hi) (j.next hj) as bs else none
    | a :: as, [] =>
      if hj : j = pat.endPos then
        none
      else
        match unconsCaseFolding (j.get hj) with
        | (b, bs) => if a == b then loop i (j.next hj) as bs else none
    | [], b :: bs =>
      if hi : i = s.endPos then
        none
      else
        match unconsCaseFolding (i.get hi) with
        | (a, as) => if a == b then loop (i.next hi) j as bs else none
  termination_by as bs => (i.remainingBytes + j.remainingBytes, as.length + bs.length)
  decreasing_by
    all_goals first
      | apply Prod.Lex.right; grind
      | apply Prod.Lex.left
        grind [String.Slice.Pos.lt_iff_remainingBytes_lt, String.Slice.Pos.lt_next]

/-!
  ## Decomposition Type and Mapping ##
-/

/-- Get canonical combining class of character

  Characters with combining class `0` are called starters. These include all
  characters that are not combining marks, as well as some combining marks.

  Unicode property: `Canonical_Combining_Class`
-/
public def getCanonicalCombiningClass (char : Char) : Nat :=
  -- ASCII shortcut
  if char.val < 0x80 then
    0
  else
    lookupCanonicalCombiningClass char.val

/-- Get full canonical decomposition of character (`NFD`)

  Returns the full canonical decomposition of the character, including for
  Hangul syllables. Returns the character itself if it has no canonical
  decomposition.

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
public def getCanonicalDecomposition (char : Char) : String :=
  -- ASCII shortcut
  if char.val < 0x80 then char.toString else
    (lookupCanonicalDecompositionMapping char.val).foldl (fun s c => s.push (Char.ofNat c.toNat)) ""

/-- Get decomposition mapping of a character

  Returns `none` if the character has no decomposition mapping. The `tag`
  field is `none` for a canonical mapping and `some _` for a compatibility
  mapping. This is a single decomposition step, not the full decomposition
  used in normalization to canonical decomposition (`NFD`) and compatibility
  decomposition (`NFKD`).

  Unicode properties:
    `Decomposition_Type`
    `Decomposition_Mapping` -/
public def getDecompositionMapping? (char : Char) : Option DecompositionMapping :=
  -- ASCII shortcut
  if char.val < 0x80 then
    none
  else
    lookupDecompositionMapping? char.val

/-!
  ## Numeric Type and Value ##
-/

/-- Check if character represents a numerical value

  This includes decimal digits and other digits.

  Unicode property: `Numeric_Type` (any value other than `None`) -/
@[inline]
public def isNumeric (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some _ => true
    | _ => otherNumeric.binSearchContains char.val (· < ·)
where
  -- CJK ideographs whose numeric values come from the Unihan database, sorted for binary search
  otherNumeric := #[
    0x3405, 0x3431, 0x3483, 0x3576, 0x382A, 0x3B4D, 0x4E00, 0x4E03, 0x4E07, 0x4E09,
    0x4E24, 0x4E59, 0x4E5D, 0x4E86, 0x4E8C, 0x4E94, 0x4E96, 0x4EAC, 0x4EBF, 0x4EC0,
    0x4EDF, 0x4EE8, 0x4F0D, 0x4F70, 0x4FC9, 0x4FE9, 0x5006, 0x5104, 0x5146, 0x5169,
    0x516B, 0x516D, 0x5200, 0x5341, 0x5343, 0x5344, 0x5345, 0x534C, 0x53C1, 0x53C2,
    0x53C3, 0x53C4, 0x53CC, 0x53F0, 0x540A, 0x5549, 0x56DB, 0x58F1, 0x58F9, 0x5954,
    0x5C1E, 0x5E7A, 0x5EFE, 0x5EFF, 0x5F0C, 0x5F0D, 0x5F0E, 0x5F10, 0x5F66, 0x62D0,
    0x62FE, 0x634C, 0x672C, 0x6761, 0x677E, 0x6797, 0x67D2, 0x6C92, 0x6CA1, 0x6D1E,
    0x6F06, 0x7396, 0x767E, 0x7695, 0x79ED, 0x7A7A, 0x7F62, 0x7F77, 0x8086, 0x80FD,
    0x842C, 0x8511, 0x8CAE, 0x8CB3, 0x8D30, 0x8FC8, 0x9081, 0x920E, 0x94A9, 0x9621,
    0x9646, 0x964C, 0x9678, 0x96F6, 0x20001, 0x20027, 0x20064, 0x200E2, 0x200E9, 0x20121,
    0x20129, 0x20136, 0x2013B, 0x2013C, 0x2052D, 0x20929, 0x2092A, 0x20983, 0x2098C, 0x2099C,
    0x209A9, 0x209B3, 0x20AEA, 0x20AFD, 0x20B19, 0x20B20, 0x20BA9, 0x20CA2, 0x22390, 0x22482,
    0x22998, 0x23B1B, 0x24F93, 0x2626D, 0x26271, 0x2629A, 0x264B9, 0x2846E, 0x28492, 0x28DC8,
    0x2B52C, 0x2B866, 0x2B871, 0x2B872, 0x2B875, 0x2B92F, 0x2B9C7, 0x2C0BD, 0x2C0F4, 0x2C65E,
    0x2C954, 0x2CB99, 0x2CEB4, 0x3000C, 0x30FD8, 0x31357, 0x31394, 0x31396, 0x31455, 0x3197A,
    0x31EC7, 0x31FA3, 0x32226, 0x32403, 0x32481, 0x324DF, 0x324E0, 0x324E8, 0x324E9, 0x3276D,
    0x32C83]

/-- Check if character represents a digit in base 10

  This includes decimal digits as well as other digits such as U+00B2
  SUPERSCRIPT TWO.

  Unicode property: `Numeric_Type=Decimal | Numeric_Type=Digit` -/
@[inline]
public def isDigit (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | some (.digit _) => true
    | _ => false

/-- Get value of digit

  Returns `none` if the character is not a digit in the sense of `isDigit`.

  Unicode properties:
    `Numeric_Type=Decimal | Numeric_Type=Digit`
    `Numeric_Value` -/
@[inline]
public def getDigit? (char : Char) : Option (Fin 10) :=
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
public def isDecimal (char : Char) : Bool :=
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
public def getDecimalRange? (char : Char) : Option (Char × Char) :=
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
public def isHexDigit (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val <= 0x0039 && char.val >= 0x0030 || -- [10] DIGIT ZERO..DIGIT NINE
  char.val <= 0x0046 && char.val >= 0x0041 || --  [6] LATIN CAPITAL LETTER A..LATIN CAPITAL LETTER F
  char.val <= 0x0066 && char.val >= 0x0061 || --  [6] LATIN SMALL LETTER A..LATIN SMALL LETTER F
  char.val <= 0xFF19 && char.val >= 0xFF10 || -- [10] FULLWIDTH DIGIT ZERO..FULLWIDTH DIGIT NINE
  char.val <= 0xFF26 && char.val >= 0xFF21 || --  [6] FULLWIDTH LATIN CAPITAL LETTER A..FULLWIDTH LATIN CAPITAL LETTER F
  char.val <= 0xFF46 && char.val >= 0xFF41    --  [6] FULLWIDTH LATIN SMALL LETTER A..FULLWIDTH LATIN SMALL LETTER F

/-- Get value of a hexadecimal digit

  Returns `none` if the character is not a hexadecimal digit in the sense of
  `isHexDigit`. Both ASCII and fullwidth forms are accepted.

  Unicode property: `Hex_Digit` -/
@[inline]
public def getHexDigit? (char : Char) : Option (Fin 16) :=
  -- Map fullwidth forms U+FF10..U+FF46 onto ASCII U+0030..U+0066
  let n := if char.toNat < 0xFF10 then char.toNat else char.toNat - 0xFEE0
  if n < 0x30 then
    none
  else if h : n - 0x30 < 10 then
    some ⟨n - 0x30, by lia⟩
  else if n < 0x41 then
    none
  else if h : n - 0x41 < 6 then
    some ⟨n - 0x41 + 10, by lia⟩
  else if n < 0x61 then
    none
  else if h : n - 0x61 < 6 then
    some ⟨n - 0x61 + 10, by lia⟩
  else
    none

/-!
  ## Other Properties ##
-/

/-- Check if noncharacter code point

  Unicode property: `Noncharacter_Code_Point`
-/
@[inline]
public def isNoncharacterCodePoint (char : Char) : Bool :=
  lookupNoncharacterCodePoint char.val

/-- Check if default ignorable character

  Unicode property: `Default_Ignorable_Code_Point`
-/
@[inline]
public def isDefaultIgnorableCodePoint (char : Char) : Bool :=
  lookupDefaultIgnorableCodePoint char.val

/-- Check if white space character

  Unicode property: `White_Space`
-/
@[inline]
public def isWhiteSpace (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char == ' ' || char >= '\t' && char <= '\r'
  else
    -- U+0085 NEXT LINE is the only non-ASCII white space outside `GC.Z`
    char.val == 0x85 || GeneralCategory.isSeparator char

/-- Check if mathematical symbol character

  Generated by `General_Category=Sm | Other_Math`.

  Unicode property: `Math` -/
@[inline]
public def isMath (char : Char) : Bool := lookupMath char.val

/-- Check if alphabetic character

  Generated by `General_Category=L | General_Category=Nl | Other_Alphabetic`.

  Unicode property: `Alphabetic` -/
@[inline]
public def isAlphabetic (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    'A' ≤ char && char ≤ 'Z' || 'a' ≤ char && char ≤ 'z'
  else
    lookupAlphabetic char.val

@[inherit_doc isAlphabetic]
public abbrev isAlpha := isAlphabetic
