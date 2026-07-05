/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasicCommon.Types.Script

@[expose] public section

namespace Unicode

/-- Structure for `ScriptExtensions.txt` table rows. -/
structure ScriptExtensionsEntry where
  lastCode : UInt32
  scripts : Array Script
deriving Inhabited, DecidableEq

end Unicode
