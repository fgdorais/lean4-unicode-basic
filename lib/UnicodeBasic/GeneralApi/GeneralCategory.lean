/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.GeneralCategory

/-!
  This file uses lookup tables:
  `GeneralCategory`.
-/

namespace Unicode

/-!
  ## General Category ##
-/

/-- Get character general category

  *Caveat*: This function never returns a derived general category. Use
  `Unicode.isInGeneralCategory` to check whether a character belongs to a
  general category (derived or not).

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
      .Zs, .Po, .Po, .Po, .Sc, .Po, .Po, .Po, .Ps, .Po, .Po, .Sm, .Po, .Pd, .Po, .Po,
      .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Nd, .Po, .Po, .Sm, .Sm, .Sm, .Po,
      .Po, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu,
      .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Lu, .Ps, .Po, .Po, .Sk, .Pc,
      .Sk, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll,
      .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ll, .Ps, .Sm, .Po, .Sm, .Cc]

public instance : Membership Char GC where
  mem cat char := getGC char ⊆ cat

public instance (char : Char) (cat : GC) : Decidable (char ∈ cat) := inferInstanceAs (Decidable (_ ⊆ _))

namespace GeneralCategory

/-- Check if letter character (`L`)

  This is a derived category (`L = Lu | Ll | Lt | Lm | Lo`).

  Unicode Property: `General_Category=L` -/
public abbrev isLetter (char : Char) : Bool := char ∈ GC.L

/-- Check if lowercase letter character (`Ll`)

  Unicode Property: `General_Category=Ll` -/
public abbrev isLowercaseLetter (char : Char) : Bool := char ∈ GC.Ll

/-- Check if titlecase letter character (`Lt`)

  Unicode Property: `General_Category=Lt` -/
public abbrev isTitlecaseLetter (char : Char) : Bool := char ∈ GC.Lt

/-- Check if uppercase letter character (`Lu`)

  Unicode Property: `General_Category=Lu` -/
public abbrev isUppercaseLetter (char : Char) : Bool := char ∈ GC.Lu

/-- Check if cased letter character (`LC`)

  This is a derived category (`L = Lu | Ll | Lt`).

  Unicode Property: `General_Category=LC` -/
public abbrev isCasedLetter (char : Char) : Bool := char ∈ GC.LC

/-- Check if modifier letter character (`Lm`)

  Unicode Property: `General_Category=Lm`-/
public abbrev isModifierLetter (char : Char) : Bool := char ∈ GC.Lm

/-- Check if other letter character (`Lo`)

  Unicode Property: `General_Category=Lo`-/
public abbrev isOtherLetter (char : Char) : Bool := char ∈ GC.Lo

/-- Check if mark character (`M`)

  This is a derived category (`M = Mn | Mc | Me`).

  Unicode Property: `General_Category=M` -/
public abbrev isMark (char : Char) : Bool := char ∈ GC.M

/-- Check if nonspacing combining mark character (`Mn`)

  Unicode Property: `General_Category=Mn` -/
public abbrev isNonspacingMark (char : Char) : Bool := char ∈ GC.Mn

/-- Check if spacing combining mark character (`Mc`)

  Unicode Property: `General_Category=Mc` -/
public abbrev isSpacingMark (char : Char) : Bool := char ∈ GC.Mc

/-- Check if enclosing combining mark character (`Me`)

  Unicode Property: `General_Category=Me` -/
public abbrev isEnclosingMark (char : Char) : Bool := char ∈ GC.Me

/-- Check if number character (`N`)

  This is a derived category (`N = Nd | Nl | No`).

  Unicode Property: `General_Category=N` -/
public abbrev isNumber (char : Char) : Bool := char ∈ GC.N

/-- Check if decimal number character (`Nd`)

  Unicode Property: `General_Category=Nd` -/
public abbrev isDecimalNumber (char : Char) : Bool := char ∈ GC.Nd

/-- Check if letter number character (`Nl`)

  Unicode Property: `General_Category=Nl` -/
public abbrev isLetterNumber (char : Char) : Bool := char ∈ GC.Nl

/-- Check if other number character (`No`)

  Unicode Property: `General_Category=No` -/
public abbrev isOtherNumber (char : Char) : Bool := char ∈ GC.No

/-- Check if punctuation character (`P`)

  This is a derived category (`P = Pc | Pd | Ps | Pe | Pi | Pf | Po`).

  Unicode Property: `General_Category=P` -/
public abbrev isPunctuation (char : Char) : Bool := char ∈ GC.P

/-- Check if connector punctuation character (`Pc`)

  Unicode Property: `General_Category=Pc` -/
public abbrev isConnectorPunctuation (char : Char) : Bool := char ∈ GC.Pc

/-- Check if dash punctuation character (`Pd`)

  Unicode Property: `General_Category=Pd` -/
public abbrev isDashPunctuation (char : Char) : Bool := char ∈ GC.Pd

/-- Check if grouping punctuation character (`PG`)

  This is a derived category (`PG = Ps | Pe`).

  Unicode Property: `General_Category=PG` -/
public abbrev isGroupPunctuation (char : Char) : Bool := char ∈ GC.PG

/-- Check if open punctuation character (`Ps`)

  Unicode Property: `General_Category=Ps` -/
public abbrev isOpenPunctuation (char : Char) : Bool := char ∈ GC.Ps

/-- Check if close punctuation character (`Pe`)

  Unicode Property: `General_Category=Pe` -/
public abbrev isClosePunctuation (char : Char) : Bool := char ∈ GC.Pe

/-- Check if quoting punctuation character (`PQ`)

  This is a derived category (`PQ = Pi | Pf`).

  Unicode Property: `General_Category=PQ` -/
public abbrev isQuotePunctuation (char : Char) : Bool := char ∈ GC.PQ

/-- Check if initial punctuation character (`Pi`)

  Unicode Property: `General_Category=Pi` -/
public abbrev isInitialPunctuation (char : Char) : Bool := char ∈ GC.Pi

/-- Check if initial punctuation character (`Pf`)

  Unicode Property: `General_Category=Pf` -/
public abbrev isFinalPunctuation (char : Char) : Bool := char ∈ GC.Pf

/-- Check if other punctuation character (`Po`)

  Unicode Property: `General_Category=Po` -/
public abbrev isOtherPunctuation (char : Char) : Bool := char ∈ GC.Po

/-- Check if symbol character (`S`)

  This is a derived category (`S = Sm | Sc | Sk | So`).

  Unicode Property: `General_Category=S` -/
public abbrev isSymbol (char : Char) : Bool := char ∈ GC.S

/-- Check if math symbol character (`Sm`)

  Unicode Property: `General_Category=Sm` -/
public abbrev isMathSymbol (char : Char) : Bool := char ∈ GC.Sm

/-- Check if currency symbol character (`Sc`)

  Unicode Property: `General_Category=Sc` -/
public abbrev isCurrencySymbol (char : Char) : Bool := char ∈ GC.Sc

/-- Check if modifier symbol character (`Sk`)

  Unicode Property: `General_Category=Sk` -/
public abbrev isModifierSymbol (char : Char) : Bool := char ∈ GC.Sk

/-- Check if other symbol character (`So`)

  Unicode Property: `General_Category=So` -/
public abbrev isOtherSymbol (char : Char) : Bool := char ∈ GC.So

/-- Check if separator character (`Z`)

  This is a derived property (`Z = Zs | Zl | Zp`).

  Unicode Property: `General_Category=Z` -/
public abbrev isSeparator (char : Char) : Bool := char ∈ GC.Z

/-- Check if space separator character (`Zs`)

  Unicode Property: `General_Category=Zs` -/
public abbrev isSpaceSeparator (char : Char) : Bool := char ∈ GC.Zs

/-- Check if line separator character (`Zl`)

  Unicode Property: `General_Category=Zl` -/
public abbrev isLineSeparator (char : Char) : Bool := char ∈ GC.Zl

/-- Check if paragraph separator character (`Zp`)

  Unicode Property: `General_Category=Zp` -/
public abbrev isParagraphSeparator (char : Char) : Bool := char ∈ GC.Zp

/-- Check if other character (`C`)

  This is a derived category (`C = Cc | Cf | Cs | Co | Cn`).

  Unicode Property: `General_Category=C` -/
public abbrev isOther (char : Char) : Bool := char ∈ GC.C

/-- Check if control character (`Cc`)

  Unicode Property: `General_Category=Cc` -/
public abbrev isControl (char : Char) : Bool := char ∈ GC.Cc

/-- Check if format character (`Cf`)

  Unicode Property: `General_Category=Cf` -/
public abbrev isFormat (char : Char) : Bool := char ∈ GC.Cf

/-- Check if surrogate character (`Cs`)

  Does not actually occur since Lean does not regard surrogate code points as characters.

  Unicode Property: `General_Category=Cs` -/
public abbrev isSurrogate (char : Char) : Bool := char ∈ GC.Cs

/-- Check if private use character (`Co`)

  Unicode Property: `General_Category=Co` -/
public abbrev isPrivateUse (char : Char) : Bool := char ∈ GC.Co

/-- Check if unassigned character (`Cn`)

  Unicode Property: `General_Category=Cn` -/
public abbrev isUnassigned (char : Char) : Bool := char ∈ GC.Cn

end GeneralCategory
end Unicode
