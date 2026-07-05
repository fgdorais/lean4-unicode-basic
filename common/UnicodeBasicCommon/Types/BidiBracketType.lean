module

namespace Unicode

/-- Bidi paired bracket type

  Unicode property: `Bidi_Paired_Bracket_Type` -/
public inductive BidiBracketType
| public openBracket
| public closeBracket
deriving Inhabited, Repr, DecidableEq, Hashable, Ord, BEq, ReflBEq, LawfulBEq

public instance : ToString BidiBracketType where
  toString
  | .openBracket => "o"
  | .closeBracket => "c"

public def BidiBracketType.ofAbbrev? (abbr : String.Slice) : Option BidiBracketType :=
  if abbr == "o" || abbr == "Open" then some openBracket
  else if abbr == "c" || abbr == "Close" then some closeBracket
  else none

@[inherit_doc BidiBracketType.ofAbbrev?]
public def BidiBracketType.ofAbbrev! (abbr : String.Slice) : BidiBracketType :=
  match ofAbbrev? abbr with
  | some bt => bt
  | none => panic! s!"invalid bidi bracket type abbreviation {abbr.copy}"
