/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

namespace UnicodeDataTest.Common

/-- A single conformance mismatch. -/
public structure Failure where
  file : String
  line : Nat
  expected : String
  actual : String
  comment : Option String := none
deriving Repr

/-- Print a conformance report and return a process exit code. -/
public def reportFailures (label : String) (failures : Array Failure) : IO UInt32 := do
  if failures.isEmpty then
    return 0
  else
    IO.eprintln s!"{label}: {failures.size} failure(s)"
    for f in failures[:10] do
      IO.eprintln s!"  {f.file}:{f.line}"
      IO.eprintln s!"    expected: {f.expected}"
      IO.eprintln s!"    actual:   {f.actual}"
      match f.comment with
      | some c => IO.eprintln s!"    comment:  {c}"
      | none => pure ()
    if failures.size > 10 then
      IO.eprintln s!"  ... {failures.size - 10} more"
    return 1

end UnicodeDataTest.Common
