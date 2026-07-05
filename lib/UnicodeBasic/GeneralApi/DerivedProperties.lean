/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.IdStart
public import UnicodeBasic.TableLookup.IdContinue
public import UnicodeBasic.TableLookup.XidStart
public import UnicodeBasic.TableLookup.XidContinue
public import UnicodeBasic.TableLookup.Dash
public import UnicodeBasic.TableLookup.Hyphen
public import UnicodeBasic.TableLookup.QuotationMark
public import UnicodeBasic.TableLookup.TerminalPunctuation
public import UnicodeBasic.TableLookup.Extender
public import UnicodeBasic.TableLookup.RegionalIndicator
public import UnicodeBasic.TableLookup.Diacritic
public import UnicodeBasic.TableLookup.SentenceTerminal
public import UnicodeBasic.TableLookup.PatternSyntax
public import UnicodeBasic.TableLookup.PatternWhiteSpace
public import UnicodeBasic.TableLookup.GraphemeBase
public import UnicodeBasic.TableLookup.GraphemeExtend

/-!
  This file uses lookup tables:
  `IdStart`, `IdContinue`, `XidStart`, `XidContinue`, `Dash`, `Hyphen`,
  `QuotationMark`, `TerminalPunctuation`, `Extender`, `RegionalIndicator`,
  `Diacritic`, `SentenceTerminal`, `PatternSyntax`, `PatternWhiteSpace`,
  `GraphemeBase`, `GraphemeExtend`.
-/

namespace Unicode

/-!
  ## Extended Properties ##
-/

/-- Check if character is an identifier start character

  Unicode property: `ID_Start` -/
@[inline]
public def isIDStart (char : Char) : Bool := lookupIDStart char.val

/-- Check if character is an identifier continue character

  Unicode property: `ID_Continue` -/
@[inline]
public def isIDContinue (char : Char) : Bool := lookupIDContinue char.val

/-- Check if character is an identifier start character

  Unicode property: `XID_Start` -/
@[inline]
public def isXIDStart (char : Char) : Bool := lookupXIDStart char.val

/-- Check if character is an identifier continue character

  Unicode property: `XID_Continue` -/
@[inline]
public def isXIDContinue (char : Char) : Bool := lookupXIDContinue char.val

/-- Check if character is a dash character

  Unicode property: `Dash` -/
@[inline]
public def isDash (char : Char) : Bool := lookupDash char.val

/-- Check if character is a hyphen character

  Unicode property: `Hyphen` -/
@[inline]
public def isHyphen (char : Char) : Bool := lookupHyphen char.val

/-- Check if character is a quotation mark character

  Unicode property: `Quotation_Mark` -/
@[inline]
public def isQuotationMark (char : Char) : Bool := lookupQuotationMark char.val

/-- Check if character is a terminal punctuation character

  Unicode property: `Terminal_Punctuation` -/
@[inline]
public def isTerminalPunctuation (char : Char) : Bool := lookupTerminalPunctuation char.val

/-- Check if character is an extender character

  Unicode property: `Extender` -/
@[inline]
public def isExtender (char : Char) : Bool := lookupExtender char.val

/-- Check if character is a regional indicator character

  Unicode property: `Regional_Indicator` -/
@[inline]
public def isRegionalIndicator (char : Char) : Bool := lookupRegionalIndicator char.val

/-- Check if character is a diacritic character

  Unicode property: `Diacritic` -/
@[inline]
public def isDiacritic (char : Char) : Bool := lookupDiacritic char.val

/-- Check if character is a sentence terminal character

  Unicode property: `Sentence_Terminal` -/
@[inline]
public def isSentenceTerminal (char : Char) : Bool := lookupSentenceTerminal char.val

/-- Check if character is a pattern syntax character

  Unicode property: `Pattern_Syntax` -/
@[inline]
public def isPatternSyntax (char : Char) : Bool := lookupPatternSyntax char.val

/-- Check if character is a pattern white space character

  Unicode property: `Pattern_White_Space` -/
@[inline]
public def isPatternWhiteSpace (char : Char) : Bool := lookupPatternWhiteSpace char.val

/-- Check if character is a grapheme base character

  Unicode property: `Grapheme_Base` -/
public def isGraphemeBase (char : Char) : Bool := lookupGraphemeBase char.val

/-- Check if character is a grapheme extender character

  Unicode property: `Grapheme_Extend` -/
public def isGraphemeExtend (char : Char) : Bool := lookupGraphemeExtend char.val

end Unicode
