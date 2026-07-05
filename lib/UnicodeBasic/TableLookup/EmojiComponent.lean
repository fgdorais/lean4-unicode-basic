/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.EmojiComponent

namespace Unicode

/-- Check if code point has Emoji_Component property using lookup table -/
public abbrev lookupEmojiComponent (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.EmojiComponent.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.EmojiComponent.IsInsideSparseRangeTable c h
  else
    False
