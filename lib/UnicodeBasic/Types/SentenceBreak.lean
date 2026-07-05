module

@[expose] public section

namespace Unicode

/-- Sentence break property

  Unicode property: `Sentence_Break` -/
inductive SentenceBreak
| aTerm
| cr
| close
| extend
| format
| lf
| lower
| numeric
| oLetter
| sContinue
| sTerm
| sep
| sp
| upper
deriving Inhabited, DecidableEq, Repr

inductive MaybeSentenceBreak where
| other : MaybeSentenceBreak
| nonOther : SentenceBreak → MaybeSentenceBreak
deriving Inhabited, DecidableEq, Repr

def SentenceBreak.ofAbbrev? (abbr : String.Slice) : Option SentenceBreak :=
  if abbr == "AT" || abbr == "ATerm" then some aTerm
  else if abbr == "CR" then some cr
  else if abbr == "CL" || abbr == "Close" then some close
  else if abbr == "EX" || abbr == "Extend" then some extend
  else if abbr == "FO" || abbr == "Format" then some format
  else if abbr == "LF" then some lf
  else if abbr == "LO" || abbr == "Lower" then some lower
  else if abbr == "NU" || abbr == "Numeric" then some numeric
  else if abbr == "LE" || abbr == "OLetter" then some oLetter
  else if abbr == "SC" || abbr == "SContinue" then some sContinue
  else if abbr == "ST" || abbr == "STerm" then some sTerm
  else if abbr == "SE" || abbr == "Sep" then some sep
  else if abbr == "SP" || abbr == "Sp" then some sp
  else if abbr == "UP" || abbr == "Upper" then some upper
  else none

@[inherit_doc SentenceBreak.ofAbbrev?]
def MaybeSentenceBreak.ofAbbrev? (abbr : String.Slice) : Option MaybeSentenceBreak :=
  if abbr == "XX" || abbr == "Other" then some .other
  else .nonOther <$> SentenceBreak.ofAbbrev? abbr

@[inherit_doc SentenceBreak.ofAbbrev?]
def SentenceBreak.ofAbbrev! (abbr : String.Slice) : SentenceBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid sentence break abbreviation {abbr.copy}"

@[inherit_doc MaybeSentenceBreak.ofAbbrev?]
def MaybeSentenceBreak.ofAbbrev! (abbr : String.Slice) : MaybeSentenceBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid sentence break abbreviation {abbr.copy}"

end Unicode

end
