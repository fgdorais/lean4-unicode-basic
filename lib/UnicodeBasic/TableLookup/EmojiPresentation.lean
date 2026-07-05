/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.EmojiPresentation

namespace Unicode

/-- Check if code point has Emoji_Presentation property using lookup table -/
public abbrev lookupEmojiPresentation (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.EmojiPresentation.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.EmojiPresentation.IsInsideSparseRangeTable c h
  else
    False
