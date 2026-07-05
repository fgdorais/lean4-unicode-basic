/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.BidiClass
public import UnicodeBasic.TableLookup.BidiMirrored

/-!
  This file uses lookup tables:
  `BidiClass`, `BidiMirrored`.
  It also contains inline data extracted from `PropList.txt` for `Bidi_Control`.
-/

namespace Unicode

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

/-- Check whether a character has a specific bidi class. -/
@[inline]
public def isBidiClass (bc : BidiClass) (char : Char) : Bool :=
  getBidiClass char == bc

/-- Check if bidirectional left-to-right character -/
@[inline]
public def isBidiLeftToRight (char : Char) : Bool := isBidiClass .L char

/-- Check if bidirectional right-to-left character -/
@[inline]
public def isBidiRightToLeft (char : Char) : Bool := isBidiClass .R char

/-- Check if bidirectional arabic letter character -/
@[inline]
public def isBidiArabicLetter (char : Char) : Bool := isBidiClass .AL char

/-- Check if bidirectional european number character -/
@[inline]
public def isBidiEuropeanNumber (char : Char) : Bool := isBidiClass .EN char

/-- Check if bidirectional arabic number character -/
@[inline]
public def isBidiArabicNumber (char : Char) : Bool := isBidiClass .AN char

/-- Check if bidirectional european separator character -/
@[inline]
public def isBidiEuropeanSeparator (char : Char) : Bool := isBidiClass .ES char

/-- Check if bidirectional european terminator character -/
@[inline]
public def isBidiEuropeanTerminator (char : Char) : Bool := isBidiClass .ET char

/-- Check if bidirectional common separator character -/
@[inline]
public def isBidiCommonSeparator (char : Char) : Bool := isBidiClass .CS char

/-- Check if bidirectional nonspacing mark character -/
@[inline]
public def isBidiNonspacingMark (char : Char) : Bool := isBidiClass .NSM char

/-- Check if bidirectional boundary neutral character -/
@[inline]
public def isBidiBoundaryNeutral (char : Char) : Bool := isBidiClass .BN char

/-- Check if bidirectional paragraph separator character -/
@[inline]
public def isBidiParagraphSeparator (char : Char) : Bool := isBidiClass .B char

/-- Check if bidirectional segment separator character -/
@[inline]
public def isBidiSegmentSeparator (char : Char) : Bool := isBidiClass .S char

/-- Check if bidirectional white space character -/
@[inline]
public def isBidiWhiteSpace (char : Char) : Bool := isBidiClass .WS char

/-- Check if bidirectional other neutral character -/
@[inline]
public def isBidiOtherNeutral (char : Char) : Bool := isBidiClass .ON char

/-- Check if bidirectional left-to-right embedding character -/
@[inline]
public def isBidiLeftToRightEmbedding (char : Char) : Bool := isBidiClass .LRE char

/-- Check if bidirectional left-to-right override character -/
@[inline]
public def isBidiLeftToRightOverride (char : Char) : Bool := isBidiClass .LRO char

/-- Check if bidirectional right-to-left embedding character -/
@[inline]
public def isBidiRightToLeftEmbedding (char : Char) : Bool := isBidiClass .RLE char

/-- Check if bidirectional right-to-left override character -/
@[inline]
public def isBidiRightToLeftOverride (char : Char) : Bool := isBidiClass .RLO char

/-- Check if bidirectional pop directional format character -/
@[inline]
public def isBidiPopDirectionalFormat (char : Char) : Bool := isBidiClass .PDF char

/-- Check if bidirectional left-to-right isolate character -/
@[inline]
public def isBidiLeftToRightIsolate (char : Char) : Bool := isBidiClass .LRI char

/-- Check if bidirectional right-to-left isolate character -/
@[inline]
public def isBidiRightToLeftIsolate (char : Char) : Bool := isBidiClass .RLI char

/-- Check if bidirectional first strong isolate character -/
@[inline]
public def isBidiFirstStrongIsolate (char : Char) : Bool := isBidiClass .FSI char

/-- Check if bidirectional pop directional isolate character -/
@[inline]
public def isBidiPopDirectionalIsolate (char : Char) : Bool := isBidiClass .PDI char

end Unicode
