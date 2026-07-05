/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Bounds

namespace Unicode

/-- Check if code point is a noncharcter code point

  Unicode property: `Noncharacter_Code_Point` -/
@[inline]
public def lookupNoncharacterCodePoint (c : UInt32) : Bool :=
  (c ≤ 0xFDEF && 0xFDD0 ≤ c) || (c ≤ Unicode.max && c &&& 0xFFFE == 0xFFFE)
