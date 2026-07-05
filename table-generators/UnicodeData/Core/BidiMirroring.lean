/-
Copyright © 2025-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Std.Data.HashMap.Basic
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

namespace BidiMirroring

/-- Raw string from `BidiMirroring.txt` -/
public def txt := include_str "../../data-ucd/core/BidiMirroring.txt"

/-- Parsed `BidiMirroring.txt` mappings. -/
public def data : Std.HashMap UInt32 UInt32 := Id.run do
  let stream := UCDStream.ofString txt
  let mut data : Std.HashMap UInt32 UInt32 := {}
  for record in stream do
    let c₀ := ofHexString! record[0]!
    let c₁ := ofHexString! record[1]!
    data := data.insert c₀ c₁
  return data

/-- Find the bidi mirroring glyph for a code point, if it exists. -/
public def lookupGlyph? (code : UInt32) : Option UInt32 :=
  data.get? code

end BidiMirroring

end Unicode
