module

@[expose] public section

namespace Unicode

/-- Word break property

  Unicode property: `Word_Break` -/
inductive WordBreak
| doubleQuote
| singleQuote
| hebrewLetter
| cr
| lf
| newline
| extend
| regionalIndicator
| katakana
| aLetter
| midLetter
| midNum
| midNumLet
| numeric
| extendNumLet
| wSegSpace
| zwj
| format
deriving Inhabited, DecidableEq, Repr

inductive MaybeWordBreak
| other
| nonOther (wb : WordBreak)
deriving Inhabited, DecidableEq, Repr

instance : ToString WordBreak where
  toString
  | .doubleQuote => "Double_Quote"
  | .singleQuote => "Single_Quote"
  | .hebrewLetter => "Hebrew_Letter"
  | .cr => "CR"
  | .lf => "LF"
  | .newline => "Newline"
  | .extend => "Extend"
  | .regionalIndicator => "Regional_Indicator"
  | .katakana => "Katakana"
  | .aLetter => "ALetter"
  | .midLetter => "MidLetter"
  | .midNum => "MidNum"
  | .midNumLet => "MidNumLet"
  | .numeric => "Numeric"
  | .extendNumLet => "ExtendNumLet"
  | .wSegSpace => "WSegSpace"
  | .zwj => "ZWJ"
  | .format => "Format"

instance : ToString MaybeWordBreak where
  toString
  | .other => "Other"
  | .nonOther wb => toString wb

def WordBreak.ofAbbrev? (abbr : String.Slice) : Option WordBreak :=
  if abbr == "DQ" || abbr == "Double_Quote" then some doubleQuote
  else if abbr == "SQ" || abbr == "Single_Quote" then some singleQuote
  else if abbr == "HL" || abbr == "Hebrew_Letter" then some hebrewLetter
  else if abbr == "CR" then some cr
  else if abbr == "LF" then some lf
  else if abbr == "NL" || abbr == "Newline" then some newline
  else if abbr == "EX" || abbr == "Extend" then some extend
  else if abbr == "RI" || abbr == "Regional_Indicator" then some regionalIndicator
  else if abbr == "KA" || abbr == "Katakana" then some katakana
  else if abbr == "LE" || abbr == "ALetter" then some aLetter
  else if abbr == "ML" || abbr == "MidLetter" then some midLetter
  else if abbr == "MN" || abbr == "MidNum" then some midNum
  else if abbr == "MB" || abbr == "MidNumLet" then some midNumLet
  else if abbr == "NU" || abbr == "Numeric" then some numeric
  else if abbr == "EX" || abbr == "ExtendNumLet" then some extendNumLet
  else if abbr == "WS" || abbr == "WSegSpace" then some wSegSpace
  else if abbr == "ZWJ" then some zwj
  else if abbr == "FO" || abbr == "Format" then some format
  else none

def MaybeWordBreak.ofAbbrev? (abbr : String.Slice) : Option MaybeWordBreak :=
  if abbr == "XX" || abbr == "Other" then some .other
  else .nonOther <$> WordBreak.ofAbbrev? abbr

@[inherit_doc WordBreak.ofAbbrev?]
def WordBreak.ofAbbrev! (abbr : String.Slice) : WordBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid word break abbreviation {abbr.copy}"

@[inherit_doc MaybeWordBreak.ofAbbrev?]
def MaybeWordBreak.ofAbbrev! (abbr : String.Slice) : MaybeWordBreak :=
  match MaybeWordBreak.ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid word break abbreviation {abbr.copy}"

end Unicode
