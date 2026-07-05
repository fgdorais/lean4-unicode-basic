module

namespace Unicode

/-- Line break property

  Unicode property: `Line_Break` -/
public inductive LineBreak
| public unknown
| public ambiguous
| public aksara
| public aksaraPrebase
| public aksaraStart
| public alphabetic
| public breakAfter
| public breakBefore
| public breakBoth
| public mandatoryBreak
| public carriageReturn
| public contingentBreak
| public closeParenthesis
| public closePunctuation
| public combiningMark
| public conditionalJapaneseStarter
| public eBase
| public eModifier
| public exclamation
| public glue
| public h2
| public h3
| public hyphen
| public unambiguousHyphen
| public hebrewLetter
| public ideographic
| public inseparable
| public infixNumeric
| public jl
| public jt
| public jv
| public lineFeed
| public nextLine
| public nonstarter
| public numeric
| public openPunctuation
| public postfixNumeric
| public prefixNumeric
| public quotation
| public regionalIndicator
| public complexContext
| public surrogate
| public space
| public breakSymbols
| public viramaFinal
| public virama
| public wordJoiner
| public zwSpace
| public zwj
deriving Inhabited, DecidableEq, Repr

public def LineBreak.ofAbbrev? (abbr : String.Slice) : Option LineBreak :=
  if abbr == "XX" then some unknown
  else if abbr == "AI" then some ambiguous
  else if abbr == "AK" then some aksara
  else if abbr == "AP" then some aksaraPrebase
  else if abbr == "AS" then some aksaraStart
  else if abbr == "AL" then some alphabetic
  else if abbr == "BA" then some breakAfter
  else if abbr == "BB" then some breakBefore
  else if abbr == "B2" then some breakBoth
  else if abbr == "BK" then some mandatoryBreak
  else if abbr == "CR" then some carriageReturn
  else if abbr == "CB" then some contingentBreak
  else if abbr == "CP" then some closeParenthesis
  else if abbr == "CL" then some closePunctuation
  else if abbr == "CM" then some combiningMark
  else if abbr == "CJ" then some conditionalJapaneseStarter
  else if abbr == "EB" then some eBase
  else if abbr == "EM" then some eModifier
  else if abbr == "EX" then some exclamation
  else if abbr == "GL" then some glue
  else if abbr == "H2" then some h2
  else if abbr == "H3" then some h3
  else if abbr == "HY" then some hyphen
  else if abbr == "HH" then some unambiguousHyphen
  else if abbr == "HL" then some hebrewLetter
  else if abbr == "ID" then some ideographic
  else if abbr == "IN" then some inseparable
  else if abbr == "IS" then some infixNumeric
  else if abbr == "JL" then some jl
  else if abbr == "JT" then some jt
  else if abbr == "JV" then some jv
  else if abbr == "LF" then some lineFeed
  else if abbr == "NL" then some nextLine
  else if abbr == "NS" then some nonstarter
  else if abbr == "NU" then some numeric
  else if abbr == "OP" then some openPunctuation
  else if abbr == "PO" then some postfixNumeric
  else if abbr == "PR" then some prefixNumeric
  else if abbr == "QU" then some quotation
  else if abbr == "RI" then some regionalIndicator
  else if abbr == "SA" then some complexContext
  else if abbr == "SG" then some surrogate
  else if abbr == "SP" then some space
  else if abbr == "SY" then some breakSymbols
  else if abbr == "VF" then some viramaFinal
  else if abbr == "VI" then some virama
  else if abbr == "WJ" then some wordJoiner
  else if abbr == "ZW" then some zwSpace
  else if abbr == "ZWJ" then some zwj
  else none

@[inherit_doc LineBreak.ofAbbrev?]
public def LineBreak.ofAbbrev! (abbr : String.Slice) : LineBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid line break abbreviation {abbr.copy}"

end Unicode
