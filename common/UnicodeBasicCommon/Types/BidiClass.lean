module

namespace Unicode

/-!
  ## Bidirectional Class ##
-/

/-- Bidirectional class

  Unicode property: `Bidi_Class` -/
public inductive BidiClass
/-- (`L`) strong left-to-right character -/
| public leftToRight
/-- (`R`) strong right-to-left (non-Arabic-type) character -/
| public rightToLeft
/-- (`AL`) strong right-to-left (Arabic-type) character -/
| public arabicLetter
/-- (`EN`) ASCII digit or Eastern Arabic-Indic digit -/
| public europeanNumber
/-- (`ES`) European separator: plus and-/
| public europeanSeparator
/-- (`ET`) European terminator in a numeric format context, includes currency signs -/
| public europeanTerminator
/-- (`AN`) Arabic-Indic digit -/
| public arabicNumber
/-- (`CS`) common separator: commas, colons, and slashes -/
| public commonSeparator
/-- (`NSM`) nonspacing mark -/
| public nonspacingMark
/-- (`BN`) boundary neutral: most format characters, control codes, or noncharacters -/
| public boundaryNeutral
/-- (`B`)	paragraph separator, various newline characters -/
| public paragraphSeparator
/-- (`S`)	segment separator, various segment-related control codes -/
| public segmentSeparator
/-- (`WS`) white spaces -/
| public whiteSpace
/-- (`ON`) other neutral: most other symbols and punctuation marks -/
| public otherNeutral
/-- (`LRE`) left to right embedding (U+202A: the LR embedding control) -/
| public leftToRightEmbedding
/-- (`LRO`)	Left_To_Right_Override	(U+202D: the LR override control) -/
| public leftToRightOverride
/-- (`RLE`) right-to-left embedding (U+202B: the RL embedding control) -/
| public rightToLeftEmbeding
/-- (`RLO`) right-to-left override (U+202E: the RL override control) -/
| public rightToLeftOverride
/-- (`PDF`) pop directional format (U+202C: terminates an embedding or override control) -/
| public popDirectionalFormat
/-- (`LRI`) left-to-right isolate (U+2066: the LR isolate control) -/
| public leftToRightIsolate
/-- (`RLI`) right-toleft isolate (U+2067: the RL isolate control) -/
| public rightToLeftIsolate
/-- (`FSI`)	first strong isolate (U+2068: the first strong isolate control) -/
| public firstStrongIsolate
/-- (`PDI`) pop directional isolate (U+2069: terminates an isolate control) -/
| public popDirectionalIsolate
deriving Inhabited, DecidableEq

/-- Bidi class: strong left-to-right (`L`) -/
public protected def BidiClass.L := leftToRight
/-- Bidi class: strong right-to-left (`R`) -/
public protected def BidiClass.R := rightToLeft
/-- Bidi class: arabic letter (`AL`) -/
public protected def BidiClass.AL := arabicLetter
/-- Bidi class: european number (`EN`) -/
public protected def BidiClass.EN := europeanNumber
/-- Bidi class: european separator (`ES`) -/
public protected def BidiClass.ES := europeanSeparator
/-- Bidi class: european terminator (`ET`) -/
public protected def BidiClass.ET := europeanTerminator
/-- Bidi class: arabic number (`AN`) -/
public protected def BidiClass.AN := arabicNumber
/-- Bidi class: common separator (`CS`) -/
public protected def BidiClass.CS := commonSeparator
/-- Bidi class: nonspacing mark (`NSM`) -/
public protected def BidiClass.NSM := nonspacingMark
/-- Bidi class: boundary neutral (`BN`) -/
public protected def BidiClass.BN := boundaryNeutral
/-- Bidi class: paragraph separator (`B`) -/
public protected def BidiClass.B := paragraphSeparator
/-- Bidi class: segment separator (`S`) -/
public protected def BidiClass.S := segmentSeparator
/-- Bidi class: white space (`WS`) -/
public protected def BidiClass.WS := whiteSpace
/-- Bidi class: other neutral (`ON`) -/
public protected def BidiClass.ON := otherNeutral
/-- Bidi class: left-to-right embedding (`LRE`) -/
public protected def BidiClass.LRE := leftToRightEmbedding
/-- Bidi class: left-to-right override (`LRO`) -/
public protected def BidiClass.LRO := leftToRightOverride
/-- Bidi class: right-to-left embedding (`RLE`) -/
public protected def BidiClass.RLE := rightToLeftEmbeding
/-- Bidi class: right-to-left override (`RLO`) -/
public protected def BidiClass.RLO := rightToLeftOverride
/-- Bidi class: pop directional format (`PDF`) -/
public protected def BidiClass.PDF := popDirectionalFormat
/-- Bidi class: left-to-right isolate (`LRI`) -/
public protected def BidiClass.LRI := leftToRightIsolate
/-- Bidi class: right-to-left isolate (`RLI`) -/
public protected def BidiClass.RLI := rightToLeftIsolate
/-- Bidi class: first strong isolate (`FSI`) -/
public protected def BidiClass.FSI := firstStrongIsolate
/-- Bidi class: pop directional isolate (`PDI`) -/
public protected def BidiClass.PDI := popDirectionalIsolate

/-- String abbreviation for bidi class -/
public def BidiClass.toAbbrev : BidiClass → String
| leftToRight => "L"
| rightToLeft => "R"
| arabicLetter => "AL"
| europeanNumber => "EN"
| europeanSeparator => "ES"
| europeanTerminator => "ET"
| arabicNumber => "AN"
| commonSeparator => "CS"
| nonspacingMark => "NSM"
| boundaryNeutral => "BN"
| paragraphSeparator => "B"
| segmentSeparator => "S"
| whiteSpace => "WS"
| otherNeutral => "ON"
| leftToRightEmbedding => "LRE"
| leftToRightOverride => "LRO"
| rightToLeftEmbeding => "RLE"
| rightToLeftOverride  => "RLO"
| popDirectionalFormat => "PDF"
| leftToRightIsolate => "LRI"
| rightToLeftIsolate => "RLI"
| firstStrongIsolate => "FSI"
| popDirectionalIsolate => "PDI"

/-- Get bidi class from abbreviation -/
public def BidiClass.ofAbbrev? (abbr : String.Slice) : Option BidiClass :=
  match abbr.chars.take 4 |>.toList with
  | ['L'] => some leftToRight
  | ['R'] => some rightToLeft
  | ['A', 'L'] => some arabicLetter
  | ['E', 'N'] => some europeanNumber
  | ['E', 'S'] => some europeanSeparator
  | ['E', 'T'] => some europeanTerminator
  | ['A', 'N'] => some arabicNumber
  | ['C', 'S'] => some commonSeparator
  | ['N', 'S', 'M'] => some nonspacingMark
  | ['B', 'N'] => some boundaryNeutral
  | ['B'] => some paragraphSeparator
  | ['S'] => some segmentSeparator
  | ['W', 'S'] => some whiteSpace
  | ['O', 'N'] => some otherNeutral
  | ['L', 'R', 'E'] => some leftToRightEmbedding
  | ['L', 'R', 'O'] => some leftToRightOverride
  | ['R', 'L', 'E'] => some rightToLeftEmbeding
  | ['R', 'L', 'O'] => some rightToLeftOverride
  | ['P', 'D', 'F'] => some popDirectionalFormat
  | ['L', 'R', 'I'] => some leftToRightIsolate
  | ['R', 'L', 'I'] => some rightToLeftIsolate
  | ['F', 'S', 'I'] => some firstStrongIsolate
  | ['P', 'D', 'I'] => some popDirectionalIsolate
  | _ => none

@[inherit_doc BidiClass.ofAbbrev?]
public def BidiClass.ofAbbrev! (abbr : String.Slice) : BidiClass :=
  match ofAbbrev? abbr with
  | some bc => bc
  | none => panic! "invalid bidi class abbreviation"

public instance : Repr BidiClass where
  reprPrec bc _ := s!"Unicode.BidiClass.{bc.toAbbrev}"

end Unicode
