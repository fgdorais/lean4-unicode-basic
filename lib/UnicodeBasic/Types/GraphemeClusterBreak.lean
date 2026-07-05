module

namespace Unicode

@[expose] public section

/-- Grapheme cluster break property

  Unicode property: `Grapheme_Cluster_Break` -/
inductive GraphemeClusterBreak
| control
| cr
| extend
| lf
| spacingMark
| prepend
| regionalIndicator
| l
| v
| t
| lv
| lvt
| zwj
deriving Inhabited, DecidableEq, Repr

inductive MaybeGraphemeClusterBreak
| nonOther (gcb : GraphemeClusterBreak)
| other
deriving Inhabited, DecidableEq, Repr

instance : ToString GraphemeClusterBreak where
  toString
  | .control => "Control"
  | .cr => "CR"
  | .extend => "Extend"
  | .lf => "LF"
  | .spacingMark => "SpacingMark"
  | .prepend => "Prepend"
  | .regionalIndicator => "Regional_Indicator"
  | .l => "L"
  | .v => "V"
  | .t => "T"
  | .lv => "LV"
  | .lvt => "LVT"
  | .zwj => "ZWJ"

instance : ToString MaybeGraphemeClusterBreak where
  toString
  | .other => "Other"
  | .nonOther gcb => toString gcb

def GraphemeClusterBreak.ofAbbrev? (abbr : String.Slice) : Option GraphemeClusterBreak :=
  if abbr == "CN" || abbr == "Control" then some control
  else if abbr == "CR" then some cr
  else if abbr == "EX" || abbr == "Extend" then some extend
  else if abbr == "LF" then some lf
  else if abbr == "SM" || abbr == "SpacingMark" then some spacingMark
  else if abbr == "PP" || abbr == "Prepend" then some prepend
  else if abbr == "RI" || abbr == "Regional_Indicator" then some regionalIndicator
  else if abbr == "L" then some l
  else if abbr == "V" then some v
  else if abbr == "T" then some t
  else if abbr == "LV" then some lv
  else if abbr == "LVT" then some lvt
  else if abbr == "ZWJ" then some zwj
  else none

def MaybeGraphemeClusterBreak.ofAbbrev? (abbr : String.Slice) : Option MaybeGraphemeClusterBreak :=
  if abbr == "XX" || abbr == "Other" then some other
  else (GraphemeClusterBreak.ofAbbrev? abbr).map nonOther

@[inherit_doc GraphemeClusterBreak.ofAbbrev?]
def GraphemeClusterBreak.ofAbbrev! (abbr : String.Slice) : GraphemeClusterBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid grapheme cluster break abbreviation {abbr.copy}"

@[inherit_doc MaybeGraphemeClusterBreak.ofAbbrev?]
def MaybeGraphemeClusterBreak.ofAbbrev! (abbr : String.Slice) : MaybeGraphemeClusterBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid grapheme cluster break abbreviation {abbr.copy}"
