/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.BidiMirroringGlyph

namespace Unicode

/-- Get the bidi mirroring glyph for a code point, if it exists.

  Unicode property: `Bidi_Mirroring_Glyph`
-/
public def lookupBidiMirroringGlyph? (c : UInt32) : Option UInt32 :=
  if h : TableLookupTables.BidiMirroringGlyph.BetweenOrEqStartEnd c then
    TableLookupTables.BidiMirroringGlyph.lookupSparsePairTable? c h
  else
    none
