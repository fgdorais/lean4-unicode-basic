/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.EmojiModifierBase

namespace Unicode

/-- Check if code point has Emoji_Modifier_Base property using lookup table -/
public abbrev lookupEmojiModifierBase (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.EmojiModifierBase.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.EmojiModifierBase.IsInsideSparseRangeTable c h
  else
    False
