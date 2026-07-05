/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.EmojiModifier

namespace Unicode

/-- Check if code point has Emoji_Modifier property using lookup table -/
public abbrev lookupEmojiModifier (c : UInt32) : Prop :=
  Unicode.TableLookupTables.EmojiModifier.BetweenOrEqStartEnd c
