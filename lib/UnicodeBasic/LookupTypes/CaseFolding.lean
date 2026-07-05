/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Unicode

/-- Structure for `CaseFolding.txt` table rows. -/
structure CaseFolding where
  mapping : String
deriving Inhabited, DecidableEq, Repr, Hashable, Ord, BEq, ReflBEq, LawfulBEq

end Unicode
