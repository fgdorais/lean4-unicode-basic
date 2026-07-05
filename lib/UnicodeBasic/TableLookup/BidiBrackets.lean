/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.BidiBracketType
public import UnicodeBasic.LookupTypes.BidiBracket
public import UnicodeBasic.TableLookupTables.BidiBrackets

namespace Unicode

/-- Get bidi bracket data for a code point.

  Unicode properties:
    `Bidi_Paired_Bracket`
    `Bidi_Paired_Bracket_Type`
-/
public def lookupBidiBracket? (c : UInt32) : Option BidiBracket :=
  if h : TableLookupTables.BidiBrackets.BetweenOrEqStartEnd c then
    TableLookupTables.BidiBrackets.lookupSparseKVTable? c h
  else
    none

/-- Get the bidi paired bracket for a code point. -/
public def lookupBidiPairedBracket? (c : UInt32) : Option UInt32 :=
  (lookupBidiBracket? c).map BidiBracket.pairedBracket

/-- Get the bidi paired bracket type for a code point. -/
public def lookupBidiPairedBracketType? (c : UInt32) : Option BidiBracketType :=
  (lookupBidiBracket? c).map BidiBracket.bracketType
