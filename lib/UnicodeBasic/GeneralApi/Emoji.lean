/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.Emoji
public import UnicodeBasic.TableLookup.EmojiPresentation
public import UnicodeBasic.TableLookup.EmojiModifier
public import UnicodeBasic.TableLookup.EmojiModifierBase
public import UnicodeBasic.TableLookup.EmojiComponent
public import UnicodeBasic.TableLookup.ExtendedPictographic

/-!
  This file uses lookup tables:
  `Emoji`, `EmojiPresentation`, `EmojiModifier`, `EmojiModifierBase`,
  `EmojiComponent`, `ExtendedPictographic`.
-/

namespace Unicode

/-!
  ## Emoji Properties ##
-/

/-- Check if character is an emoji

  Unicode property: `Emoji` -/
@[inline]
public def isEmoji (char : Char) : Bool := lookupEmoji char.val

/-- Check if character has emoji presentation by default

  Unicode property: `Emoji_Presentation` -/
@[inline]
public def isEmojiPresentation (char : Char) : Bool := lookupEmojiPresentation char.val

/-- Check if character is an emoji modifier

  Unicode property: `Emoji_Modifier` -/
@[inline]
public def isEmojiModifier (char : Char) : Bool := lookupEmojiModifier char.val

/-- Check if character is an emoji modifier base

  Unicode property: `Emoji_Modifier_Base` -/
@[inline]
public def isEmojiModifierBase (char : Char) : Bool := lookupEmojiModifierBase char.val

/-- Check if character is an emoji component

  Unicode property: `Emoji_Component` -/
@[inline]
public def isEmojiComponent (char : Char) : Bool := lookupEmojiComponent char.val

/-- Check if character is an extended pictographic character

  Unicode property: `Extended_Pictographic` -/
@[inline]
public def isExtendedPictographic (char : Char) : Bool := lookupExtendedPictographic char.val

end Unicode
