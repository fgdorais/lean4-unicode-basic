/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.Name
public import UnicodeBasic.TableLookup.BlockName
public import UnicodeBasic.TableLookup.EastAsianWidth
public import UnicodeBasic.TableLookup.VerticalOrientation
public import UnicodeBasic.TableLookup.BidiBrackets
public import UnicodeBasic.TableLookup.BidiMirroringGlyph


/-!
  This file uses lookup tables:
  `Name`, `BlockName`, `EastAsianWidth`, `VerticalOrientation`,
  `BidiBrackets`, `BidiMirroringGlyph`.
-/

namespace Unicode

/-!
  ## Name ##
-/

/-- Get character name

  When the Unicode property `Name` is empty, a unique code label is returned
  as recommended in Unicode Standard, section 4.8. These labels start with
  `'<'` (U+003C) and end with `'>'` (U+003E) so they are distinguishable from
  actual name values.

  Unicode property: `Name`
-/
@[inline]
public def getName (char : Char) : String := lookupName char.val

/-!
  ## Block ##
-/

/-- Get Unicode block name -/
public def getBlockName (char : Char) : String := toString (lookupBlockName char.val)

/-!
  ## East Asian Width ##
-/

/-- Get East Asian width -/
public def getEastAsianWidth (char : Char) : EastAsianWidth :=
  lookupEastAsianWidth char.val

/-!
  ## Vertical Orientation ##
-/

/-- Get vertical orientation -/
public def getVerticalOrientation (char : Char) : VerticalOrientation :=
  lookupVerticalOrientation char.val

/-!
  ## Bidi Brackets ##
-/

/-- Get bidi paired bracket -/
public def getBidiPairedBracket? (char : Char) : Option UInt32 :=
  lookupBidiPairedBracket? char.val

/-- Get bidi paired bracket type -/
public def getBidiPairedBracketType? (char : Char) : Option BidiBracketType :=
  lookupBidiPairedBracketType? char.val

/-- Get bidi mirroring glyph code point, if any. -/
public def getBidiMirroringGlyph? (char : Char) : Option UInt32 :=
  lookupBidiMirroringGlyph? char.val

end Unicode
