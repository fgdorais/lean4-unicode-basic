/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import UnicodeBasic.Bidi.Resolve

/-!
  # Bidirectional Resolution

  This module implements the core Unicode Bidirectional Algorithm (UAX #9) in
  Lean and exposes a small public API for resolving embedding levels and visual
  order.
-/
