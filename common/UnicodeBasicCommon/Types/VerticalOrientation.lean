module

namespace Unicode

/-- Vertical orientation

  Unicode property: `Vertical_Orientation` -/
public inductive VerticalOrientation
| public upright
| public rotated
| public transformedUpright
| public transformedRotated
deriving Inhabited, DecidableEq

public def VerticalOrientation.toAbbrev : VerticalOrientation → String
| upright => "U"
| rotated => "R"
| transformedUpright => "Tu"
| transformedRotated => "Tr"

public instance : ToString VerticalOrientation where
  toString := VerticalOrientation.toAbbrev

public def VerticalOrientation.ofAbbrev? (abbr : String.Slice) : Option VerticalOrientation :=
  if abbr == "U" || abbr == "Upright" then some upright
  else if abbr == "R" || abbr == "Rotated" then some rotated
  else if abbr == "Tu" || abbr == "TransformedUpright" then some transformedUpright
  else if abbr == "Tr" || abbr == "TransformedRotated" then some transformedRotated
  else none

@[inherit_doc VerticalOrientation.ofAbbrev?]
public def VerticalOrientation.ofAbbrev! (abbr : String.Slice) : VerticalOrientation :=
  match ofAbbrev? abbr with
  | some vo => vo
  | none => panic! s!"invalid vertical orientation abbreviation {abbr.copy}"

public instance : Repr VerticalOrientation where
  reprPrec vo _ := s!"Unicode.VerticalOrientation.{vo.toAbbrev}"
