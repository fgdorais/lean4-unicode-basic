module

namespace Unicode

/-- East Asian width

  Unicode property: `East_Asian_Width` -/
public inductive EastAsianWidth
| public ambiguous
| public fullwidth
| public halfwidth
| public neutral
| public narrow
| public wide
deriving Inhabited, DecidableEq

public def EastAsianWidth.toAbbrev : EastAsianWidth → String
| ambiguous => "A"
| fullwidth => "F"
| halfwidth => "H"
| neutral => "N"
| narrow => "Na"
| wide => "W"

public instance : ToString EastAsianWidth where
  toString := EastAsianWidth.toAbbrev

public def EastAsianWidth.ofAbbrev? (abbr : String.Slice) : Option EastAsianWidth :=
  if abbr == "A" || abbr == "Ambiguous" then some ambiguous
  else if abbr == "F" || abbr == "Fullwidth" then some fullwidth
  else if abbr == "H" || abbr == "Halfwidth" then some halfwidth
  else if abbr == "N" || abbr == "Neutral" then some neutral
  else if abbr == "Na" || abbr == "Narrow" then some narrow
  else if abbr == "W" || abbr == "Wide" then some wide
  else none

@[inherit_doc EastAsianWidth.ofAbbrev?]
public def EastAsianWidth.ofAbbrev! (abbr : String.Slice) : EastAsianWidth :=
  match ofAbbrev? abbr with
  | some ew => ew
  | none => panic! s!"invalid east asian width abbreviation {abbr.copy}"

public instance : Repr EastAsianWidth where
  reprPrec ew _ := s!"Unicode.EastAsianWidth.{ew.toAbbrev}"
