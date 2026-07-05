module
public import UnicodeBasicCommon.Types.Script
public import UnicodeBasicCommon.Types.Script.Common
public import UnicodeBasicCommon.Types.Script.IsValidCodePoint

@[expose] public section

namespace Unicode

/-!
  ## Scripts With Unknown ##
-/

/-- Script identifier type that also admits `Zzzz` (`Unknown`). -/
structure MaybeUnknownScript where
  code : UInt32
  is_valid : Script.IsValidMaybeUnknownCodePoint code := by decide
deriving DecidableEq, Hashable

namespace MaybeUnknownScript

/-- Widen an assigned script to a maybe-unknown script. -/
@[inline]
def ofScript (s : Script) : MaybeUnknownScript :=
  MaybeUnknownScript.mk (Script.code s) (Or.inl s.is_valid)

/-- Default value is `Zzzz` (`Unknown`) -/
instance : Inhabited MaybeUnknownScript where
  default := {
    code := Script.CodePoints.unknown
    is_valid := by decide
  }

/-- String abbreviation of script -/
@[inline]
def toAbbrev (s : MaybeUnknownScript) : String := Unicode.Script.Common.toAbbrevImpl s.code

/-- Get script from abbreviation, including `Zzzz`. -/
@[inline]
def ofAbbrev? (abbr : String.Slice) : Option MaybeUnknownScript :=
  match Unicode.Script.Common.ofAbbrevAux abbr with
  | some code =>
    if h_val : Script.IsValidMaybeUnknownCodePoint code then
      some ⟨code, h_val⟩
    else
      none
  | none => none

@[inline, inherit_doc ofAbbrev?]
def ofAbbrev! (abbr : String.Slice) : MaybeUnknownScript := ofAbbrev? abbr |>.get!
