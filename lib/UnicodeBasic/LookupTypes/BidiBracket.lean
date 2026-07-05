/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasicCommon.Types.BidiBracketType

@[expose] public section

namespace Unicode

/-- Structure for `BidiBrackets.txt` table rows. -/
structure BidiBracket where
  pairedBracket : UInt32
  bracketType : BidiBracketType
deriving Inhabited, Repr, DecidableEq, Hashable, Ord, BEq, ReflBEq, LawfulBEq

end Unicode
