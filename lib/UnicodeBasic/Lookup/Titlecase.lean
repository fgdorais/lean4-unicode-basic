/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.GeneralCategory

namespace Unicode

/-- Check if code point is a titlecase letter using lookup table

  Unicode property: `Titlecase` -/
@[inline]
public def lookupTitlecase (c : UInt32) : Bool :=
  lookupGC c == GC.Lt
