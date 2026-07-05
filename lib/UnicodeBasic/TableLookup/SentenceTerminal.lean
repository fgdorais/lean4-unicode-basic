/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.SentenceTerminal

namespace Unicode

/-- Check if code point has Sentence_Terminal property using lookup table -/
public abbrev lookupSentenceTerminal (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.SentenceTerminal.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.SentenceTerminal.IsInsideSparseRangeTable c h
  else
    False
