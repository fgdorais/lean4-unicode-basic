module
public import UnicodeBasicCommon.Types.Script.Common
public import UnicodeBasicCommon.Types.Script.IsValidCodePoint

@[expose] public section

namespace Unicode

/-!
  ## Scripts ##
-/

/-- Script identifier type -/
structure Script where
  code : UInt32
  is_valid : Script.IsValidCodePoint code := by decide
deriving DecidableEq, Hashable

namespace Script

/-- Default value is `Zyyy` (`Common`) -/
instance : Inhabited Script where
  default := {
    code := Script.CodePoints.common
    is_valid := by decide
  }

/-- String abbreviation of script -/
@[inline]
def toAbbrev (s : Script) : String := Unicode.Script.Common.toAbbrevImpl s.code

/-- Get script from abbreviation -/
@[inline]
def ofAbbrev? (abbr : String.Slice) : Option Script :=
  match Unicode.Script.Common.ofAbbrevAux abbr with
  | some code =>
    if h_val : IsValidCodePoint code then
      some ⟨code, h_val⟩
    else
      none
  | none => none

@[inline, inherit_doc ofAbbrev?]
def ofAbbrev! (abbr : String.Slice) : Script := ofAbbrev? abbr |>.get!
