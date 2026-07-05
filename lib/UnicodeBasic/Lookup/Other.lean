/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.OtherAlphabetic
public import UnicodeBasic.TableLookup.OtherLowercase
public import UnicodeBasic.TableLookup.OtherMath
public import UnicodeBasic.TableLookup.OtherUppercase

namespace Unicode

/-- Get other properties using lookup table

  Unicode properties: `Other_Alphabetic`, `Other_Lowercase`, `Other_Uppercase`, `Other_Math` -/
public def lookupOther (c : UInt32) : UInt32 :=
  let bits := (0 : UInt32)
  let bits := if lookupOtherUppercase c then bits ||| 1 else bits
  let bits := if lookupOtherLowercase c then bits ||| 2 else bits
  let bits := if lookupOtherAlphabetic c then bits ||| 4 else bits
  if lookupOtherMath c then bits ||| 8 else bits
