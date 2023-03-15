/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-- Low-level conversion from `UInt32` to `Char` (*unsafe*)

  This function translates to a no-op in the compiler. However, it does not
  check whether the `UInt32` code is a valid `Char` value. Only use where it's
  known for external reasons that the code is valid. -/
protected unsafe def Char.mkUnsafe : UInt32 → Char := unsafeCast

namespace Unicode

/-- Maximum valid code point value -/
protected def max : UInt32 := 0x10FFFF

/-- Hexadecimal string representation of a code point

  Same as `toHexString` but without the `U+` prefix. -/
def toHexStringAux (code : UInt32) : String := Id.run do
  let hex := #['0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F']
  let mut code := code
  let mut dgts := []
  for _ in [:4] do
    dgts := hex[(code &&& 0xF).toNat]! :: dgts
    code := code >>> 4
  while code != 0 do
    dgts := hex[(code &&& 0xF).toNat]! :: dgts
    code := code >>> 4
  return String.mk dgts

/-- Hexadecimal string representation of a code point

  Prefix `U+` followed by at least four uppercase hexadecimal digits
  (e.g. `U+0123` and `U+4B0A1` but neither `U+123` nor `U+4b0a1`).
-/
@[inline]
def toHexString (code : UInt32) : String :=
  "U+" ++ toHexStringAux code

/-- Get code point from hexadecimal string representation

  For convenience, the `U+` prefix may be omitted and lowercase hexadecimal
  digits are accepted.
-/
def ofHexString? (str : String) : Option UInt32 := do
  let str := if "U+".isPrefixOf str then str.drop 2 else str
  if str.isEmpty || str.length > 8 then none else
    let mut val : UInt32 := 0
    for dgt in str.toSubstring do
      val := (val <<< 4) + (← hexValue? dgt)
    some val

where

  /-- Get value of hex digit -/
  @[inline] hexValue? (dgt : Char) : Option UInt32 := do
    if dgt.val < '0'.val then none else
      let mut n := dgt.val - '0'.val
      if n < 10 then
        some n
      else if dgt.val < 'A'.val then none else
        n := n - ('A'.val - '9'.val - 1)
        if n < 16 then
          some n
        else if dgt.val < 'a'.val then none else
          n := n - ('a'.val - 'A'.val)
          if n < 16 then
            some n
          else
            none

@[inherit_doc ofHexString?]
def ofHexString! (str : String) : UInt32 :=
  match ofHexString? str with
  | some val => val
  | none => panic! "invalid unicode hexadecimal string representation"

/-!
  ## General Category ##
-/

/-- Major general category (`L`, `M`, `N`, `P`, `S`, `Z`, `C`)

  Unicode property: `General_Category` -/
inductive MajorGeneralCategory : Type
/-- (`L`) Letter -/
| letter
/-- (`M`) Mark -/
| mark
/-- (`N`) Number -/
| number
/-- (`P`) Punctuation -/
| punctuation
/-- (`S`) Symbol -/
| symbol
/-- (`Z`) Separator -/
| separator
/-- (`C`) Other -/
| other
deriving Inhabited, DecidableEq

/-- String abbreviation for major general category -/
def MajorGeneralCategory.toAbbrev : MajorGeneralCategory → String
| letter => "L"
| mark => "M"
| number => "N"
| punctuation => "P"
| symbol => "S"
| separator => "Z"
| other => "C"

/-- Minor general category

  Unicode property: `General_Category` -/
inductive MinorGeneralCategory : MajorGeneralCategory → Type
/-- (`LC`) cased letter (derived from `Lu | Ll | Lt`) -/
| casedLetter : MinorGeneralCategory .letter
/-- (`Lu`) uppercase letter -/
| uppercaseLetter : MinorGeneralCategory .letter
/-- (`Ll`) lowercase letter -/
| lowercaseLetter : MinorGeneralCategory .letter
/-- (`Lt`) titlecase letter: digraphic character, with first part uppercase -/
| titlecaseLetter : MinorGeneralCategory .letter
/-- (`Lm`) modifier letter -/
| modifierLetter : MinorGeneralCategory .letter
/-- (`Lo`) other letters, including syllables and ideographs -/
| otherLetter : MinorGeneralCategory .letter
/-- (`Mn`) nonspacing combining mark (zero advance width) -/
| nonspacingMark : MinorGeneralCategory .mark
/-- (`Mc`) spacing combining mark (positive advance width) -/
| spacingMark : MinorGeneralCategory .mark
/-- (`Me`) enclosing combining mark -/
| enclosingMark : MinorGeneralCategory .mark
/-- (`Nd`) decimal digit -/
| decimalNumber : MinorGeneralCategory .number
/-- (`Nl`) letter number: a letterlike numeric character -/
| letterNumber : MinorGeneralCategory .number
/-- (`No`) numeric character of other type -/
| otherNumber : MinorGeneralCategory .number
/-- (`Pc`) connecting punctuation mark, like a tie -/
| connectorPunctuation : MinorGeneralCategory .punctuation
/-- (`Pd`) dash or hyphen punctuation mark -/
| dashPunctuation : MinorGeneralCategory .punctuation
/-- (`Ps`) opening punctuation mark (of a pair) -/
| openPunctuation : MinorGeneralCategory .punctuation
/-- (`Pe`) closing punctuation mark (of a pair) -/
| closePunctuation : MinorGeneralCategory .punctuation
/-- (`Pi`) initial quotation mark -/
| initialPunctuation : MinorGeneralCategory .punctuation
/-- (`Pf`) final quotation mark -/
| finalPunctuation : MinorGeneralCategory .punctuation
/-- (`Po`) punctuation mark of other type -/
| otherPunctuation : MinorGeneralCategory .punctuation
/-- (`Sm`) symbol of mathematical use -/
| mathSymbol : MinorGeneralCategory .symbol
/-- (`Sc`) currency sign -/
| currencySymbol : MinorGeneralCategory .symbol
/-- (`Sk`) non-letterlike modifier symbol -/
| modifierSymbol : MinorGeneralCategory .symbol
/-- (`So`) symbol of other type -/
| otherSymbol : MinorGeneralCategory .symbol
/-- (`Zs`) space character (of various non-zero widths) -/
| spaceSeparator : MinorGeneralCategory .separator
/-- (`Zl`) line separator (U+2028 LINE SEPARATOR only) -/
| lineSeparator : MinorGeneralCategory .separator
/-- (`Zp`) paragraph separator (U+2029 PARAGRAPH SEPARATOR only) -/
| paragraphSeparator : MinorGeneralCategory .separator
/-- (`Cc`) C0 or C1 control code -/
| control : MinorGeneralCategory .other
/-- (`Cf`) format control character -/
| format : MinorGeneralCategory .other
/-- (`Cs`) surrogate code point -/
| surrogate : MinorGeneralCategory .other
/-- (`Co`) private-use character -/
| privateUse : MinorGeneralCategory .other
/-- (`Cn`) reserved unassigned code point or a noncharacter -/
| unassigned : MinorGeneralCategory .other
deriving DecidableEq

/-- General category of a code point

  Unicode property: `General_Category` -/
structure GeneralCategory : Type where
  /-- Major general category of a code point -/
  major : MajorGeneralCategory
  /-- Minor general category of a code point -/
  minor : Option (MinorGeneralCategory major)
deriving Inhabited, DecidableEq

/-- General category: letter (`L`) -/
protected def GeneralCategory.L  : GeneralCategory := ⟨.letter, none⟩
/-- General category: cased letter (`LC`) -/
protected def GeneralCategory.LC : GeneralCategory := ⟨_, some .casedLetter⟩
/-- General category: uppercase letter (`Lu`) -/
protected def GeneralCategory.Lu : GeneralCategory := ⟨_, some .uppercaseLetter⟩
/-- General category: lowercase letter (`Ll`) -/
protected def GeneralCategory.Ll : GeneralCategory := ⟨_, some .lowercaseLetter⟩
/-- General category: titlecase letter (`Lt`) -/
protected def GeneralCategory.Lt : GeneralCategory := ⟨_, some .titlecaseLetter⟩
/-- General category: modifier letter (`Lm`) -/
protected def GeneralCategory.Lm : GeneralCategory := ⟨_, some .modifierLetter⟩
/-- General category: other letter (`Lo`) -/
protected def GeneralCategory.Lo : GeneralCategory := ⟨_, some .otherLetter⟩
/-- General category mark (`M`) -/
protected def GeneralCategory.M  : GeneralCategory := ⟨.mark, none⟩
/-- General category: nonspacing combining mark (`Mn`) -/
protected def GeneralCategory.Mn : GeneralCategory := ⟨_, some .nonspacingMark⟩
/-- General category: spacing combining mark (`Mc`) -/
protected def GeneralCategory.Mc : GeneralCategory := ⟨_, some .spacingMark⟩
/-- General category: enclosing combining mark (`Me`) -/
protected def GeneralCategory.Me : GeneralCategory := ⟨_, some .enclosingMark⟩
/-- General category: number (`N`) -/
protected def GeneralCategory.N  : GeneralCategory := ⟨.number, none⟩
/-- General category: decimal digit (`Nd`) -/
protected def GeneralCategory.Nd : GeneralCategory := ⟨_, some .decimalNumber⟩
/-- General category: letter number (`Nl`) -/
protected def GeneralCategory.Nl : GeneralCategory := ⟨_, some .letterNumber⟩
/-- General category: other number (`No`) -/
protected def GeneralCategory.No : GeneralCategory := ⟨_, some .otherNumber⟩
/-- General category: punctuation (`P`) -/
protected def GeneralCategory.P  : GeneralCategory := ⟨.punctuation, none⟩
/-- General category: connector punctuation (`Pc`) -/
protected def GeneralCategory.Pc : GeneralCategory := ⟨_, some .connectorPunctuation⟩
/-- General category: dash punctuation (`Pd`) -/
protected def GeneralCategory.Pd : GeneralCategory := ⟨_, some .dashPunctuation⟩
/-- General category: opening punctuation (`Ps`) -/
protected def GeneralCategory.Ps : GeneralCategory := ⟨_, some .openPunctuation⟩
/-- General category: closing punctuation (`Pe`) -/
protected def GeneralCategory.Pe : GeneralCategory := ⟨_, some .closePunctuation⟩
/-- General category: initial punctuation (`Pi`) -/
protected def GeneralCategory.Pi : GeneralCategory := ⟨_, some .initialPunctuation⟩
/-- General category: final punctuation (`Pf`) -/
protected def GeneralCategory.Pf : GeneralCategory := ⟨_, some .finalPunctuation⟩
/-- General category: other punctuation (`Po`) -/
protected def GeneralCategory.Po : GeneralCategory := ⟨_, some .otherPunctuation⟩
/-- General category: symbol (`S`) -/
protected def GeneralCategory.S  : GeneralCategory := ⟨.symbol, none⟩
/-- General category: math symbol (`Sm`) -/
protected def GeneralCategory.Sm : GeneralCategory := ⟨_, some .mathSymbol⟩
/-- General category: currency symbol (`Sc`) -/
protected def GeneralCategory.Sc : GeneralCategory := ⟨_, some .currencySymbol⟩
/-- General category: modifier symbol (`Sk`) -/
protected def GeneralCategory.Sk : GeneralCategory := ⟨_, some .modifierSymbol⟩
/-- General category: other symbol (`So`) -/
protected def GeneralCategory.So : GeneralCategory := ⟨_, some .otherSymbol⟩
/-- General category: separator (`Z`) -/
protected def GeneralCategory.Z  : GeneralCategory := ⟨.separator, none⟩
/-- General category: space separator (`Zs`) -/
protected def GeneralCategory.Zs : GeneralCategory := ⟨_, some .spaceSeparator⟩
/-- General category: line separator (`Zl`) -/
protected def GeneralCategory.Zl : GeneralCategory := ⟨_, some .lineSeparator⟩
/-- General category: paragraph separator (`Zp`) -/
protected def GeneralCategory.Zp : GeneralCategory := ⟨_, some .paragraphSeparator⟩
/-- General category: other (`C`) -/
protected def GeneralCategory.C  : GeneralCategory := ⟨.other, none⟩
/-- General category: control (`Cc`) -/
protected def GeneralCategory.Cc : GeneralCategory := ⟨_, some .control⟩
/-- General category: format (`Cf`) -/
protected def GeneralCategory.Cf : GeneralCategory := ⟨_, some .format⟩
/-- General category: surrogate (`Cs`) -/
protected def GeneralCategory.Cs : GeneralCategory := ⟨_, some .surrogate⟩
/-- General category: private use (`Co`) -/
protected def GeneralCategory.Co : GeneralCategory := ⟨_, some .privateUse⟩
/-- General category: unassigned (`Cn`) -/
protected def GeneralCategory.Cn : GeneralCategory := ⟨_, some .unassigned⟩

/-- String abbreviation for general category -/
def GeneralCategory.toAbbrev : GeneralCategory → String
| ⟨.letter, none⟩ => "L"
| ⟨_, some .casedLetter⟩ => "LC"
| ⟨_, some .uppercaseLetter⟩ => "Lu"
| ⟨_, some .lowercaseLetter⟩ => "Ll"
| ⟨_, some .titlecaseLetter⟩ => "Lt"
| ⟨_, some .modifierLetter⟩ => "Lm"
| ⟨_, some .otherLetter⟩ => "Lo"
| ⟨.mark, none⟩ => "M"
| ⟨_, some .nonspacingMark⟩ => "Mn"
| ⟨_, some .spacingMark⟩ => "Mc"
| ⟨_, some .enclosingMark⟩ => "Me"
| ⟨.number, none⟩ => "N"
| ⟨_, some .decimalNumber⟩ => "Nd"
| ⟨_, some .letterNumber⟩ => "Nl"
| ⟨_, some .otherNumber⟩ => "No"
| ⟨.punctuation, none⟩ => "P"
| ⟨_, some .connectorPunctuation⟩ => "Pc"
| ⟨_, some .dashPunctuation⟩ => "Pd"
| ⟨_, some .openPunctuation⟩ => "Ps"
| ⟨_, some .closePunctuation⟩ => "Pe"
| ⟨_, some .initialPunctuation⟩ => "Pi"
| ⟨_, some .finalPunctuation⟩ => "Pf"
| ⟨_, some .otherPunctuation⟩ => "Po"
| ⟨.symbol, none⟩ => "S"
| ⟨_, some .mathSymbol⟩ => "Sm"
| ⟨_, some .currencySymbol⟩ => "Sc"
| ⟨_, some .modifierSymbol⟩ => "Sk"
| ⟨_, some .otherSymbol⟩ => "So"
| ⟨.separator, none⟩ => "Z"
| ⟨_, some .spaceSeparator⟩ => "Zs"
| ⟨_, some .lineSeparator⟩ => "Zl"
| ⟨_, some .paragraphSeparator⟩ => "Zp"
| ⟨.other, none⟩ => "C"
| ⟨_, some .control⟩ => "Cc"
| ⟨_, some .format⟩ => "Cf"
| ⟨_, some .surrogate⟩ => "Cs"
| ⟨_, some .privateUse⟩ => "Co"
| ⟨_, some .unassigned⟩ => "Cn"

/-- Get general category from string abbreviation -/
def GeneralCategory.ofAbbrev? : String → Option GeneralCategory
| "L"  => some ⟨.letter, none⟩
| "LC" => some ⟨_, some .casedLetter⟩
| "Lu" => some ⟨_, some .uppercaseLetter⟩
| "Ll" => some ⟨_, some .lowercaseLetter⟩
| "Lt" => some ⟨_, some .titlecaseLetter⟩
| "Lm" => some ⟨_, some .modifierLetter⟩
| "Lo" => some ⟨_, some .otherLetter⟩
| "M"  => some ⟨.mark, none⟩
| "Mn" => some ⟨_, some .nonspacingMark⟩
| "Mc" => some ⟨_, some .spacingMark⟩
| "Me" => some ⟨_, some .enclosingMark⟩
| "N"  => some ⟨.number, none⟩
| "Nd" => some ⟨_, some .decimalNumber⟩
| "Nl" => some ⟨_, some .letterNumber⟩
| "No" => some ⟨_, some .otherNumber⟩
| "P"  => some ⟨.punctuation, none⟩
| "Pc" => some ⟨_, some .connectorPunctuation⟩
| "Pd" => some ⟨_, some .dashPunctuation⟩
| "Ps" => some ⟨_, some .openPunctuation⟩
| "Pe" => some ⟨_, some .closePunctuation⟩
| "Pi" => some ⟨_, some .initialPunctuation⟩
| "Pf" => some ⟨_, some .finalPunctuation⟩
| "Po" => some ⟨_, some .otherPunctuation⟩
| "S"  => some ⟨.symbol, none⟩
| "Sm" => some ⟨_, some .mathSymbol⟩
| "Sc" => some ⟨_, some .currencySymbol⟩
| "Sk" => some ⟨_, some .modifierSymbol⟩
| "So" => some ⟨_, some .otherSymbol⟩
| "Z"  => some ⟨.separator, none⟩
| "Zs" => some ⟨_, some .spaceSeparator⟩
| "Zl" => some ⟨_, some .lineSeparator⟩
| "Zp" => some ⟨_, some .paragraphSeparator⟩
| "C"  => some ⟨.other, none⟩
| "Cc" => some ⟨_, some .control⟩
| "Cf" => some ⟨_, some .format⟩
| "Cs" => some ⟨_, some .surrogate⟩
| "Co" => some ⟨_, some .privateUse⟩
| "Cn" => some ⟨_, some .unassigned⟩
| _ => none

@[inherit_doc GeneralCategory.ofAbbrev?]
def GeneralCategory.ofAbbrev! (s : String) : GeneralCategory :=
  match ofAbbrev? s with
  | some gc => gc
  | none => panic! "invalid general category abbreviation"

instance : Repr GeneralCategory where
  reprPrec gc _ := s!"Unicode.GeneralCategory.{gc.toAbbrev}"

/-!
  ## Numeric Type and Value ##
-/

/-- Unicode numeric type

  Unicode properties: `Numeric_Type`, `Numeric_Value` -/
inductive NumericType
/-- Decimal digit type and value -/
| decimal (value : Fin 10) : NumericType
/-- Digit type and value -/
| digit (value : Fin 10) : NumericType
/-- Numeric type and value -/
| numeric (num : Int) (den : Option Nat) : NumericType
deriving Inhabited, DecidableEq, Repr

/-- Decimal digit type

  The character is part of a sequence of contiguous code points representing
  decimal digits 0 through 9.

  Unicode property: `Numeric_Type`
-/
def NumericType.isDecimal : NumericType → Bool
| decimal _ => true
| _ => false

/-- Digit type

  The character represents a decimal digit 0 through 9, but may need special handling.

  Unicode property: `Numeric_Type`
-/
def NumericType.isDigit : NumericType → Bool
| decimal _ => true
| digit _ => true
| _ => false

/-- Get the value of a numeric type

  Returns either an integer value or a numerator-denominator pair representing a rational value.

  Unicode property: `Numeric_Value`
-/
def NumericType.value : NumericType → Int ⊕ Int × Nat
| decimal n => .inl n
| digit n => .inl n
| numeric n none => .inl n
| numeric n (some d) => .inr (n, d)

/-!
  ## Decomposition Mapping ##
-/

/-- Compatibility format tag

  Unicode properties: `Decomposition_Type`, `Decomposition_Mapping` -/
inductive CompatibilityTag
/-- Font variant -/
| font
/-- No-break version of a space or hyphen -/
| noBreak
/-- Initial presentation form (Arabic) -/
| initial
/-- Medial presentation form (Arabic) -/
| medial
/-- Final presentation form (Arabic) -/
| final
/-- Isolated presentation form (Arabic) -/
| isolated
/-- Encircled form -/
| circle
/-- Superscript form -/
| super
/-- Subscript form -/
| sub
/-- Vertical layout presentation form -/
| vertical
/-- Wide (or zenkaku) compatibility character -/
| wide
/-- Narrow (or hankaku) compatibility character -/
| narrow
/-- Small variant form (CNS compatibility) -/
| small
/-- CJK squared font variant -/
| square
/-- Vulgar fraction form -/
| fraction
/-- Otherwise unspecified compatibility character -/
| compat
deriving Inhabited, Repr

instance : ToString CompatibilityTag where
  toString
  | .font => "<font>"
  | .noBreak => "<noBreak>"
  | .initial => "<initial>"
  | .medial => "<medial>"
  | .final => "<final>"
  | .isolated => "<isolated>"
  | .circle => "<circle>"
  | .super => "<super>"
  | .sub => "<sub>"
  | .vertical => "<vertical>"
  | .wide => "<wide>"
  | .narrow => "<narrow>"
  | .small => "<small>"
  | .square => "<square>"
  | .fraction => "<fraction>"
  | .compat => "<compat>"

/-- Decomposition maping

  Unicode properties: `Decomposition_Type`, `Decomposition_Mapping` -/
structure DecompositionMapping where
  /-- Compatibility format tag -/
  tag : Option CompatibilityTag
  /-- Decomposition mapping -/
  mapping : List Char
deriving Inhabited, Repr

/-!
  ## Bidirectional Class ##
-/

/-- Bidirectional class

  Unicode property: `BIDI_CLASS` -/
inductive BidiClass
/-- (`L`) strong left-to-right character -/
| leftToRight
/-- (`R`) strong right-to-left (non-Arabic-type) character -/
| rightToLeft
/-- (`AL`) strong right-to-left (Arabic-type) character -/
| arabicLetter
/-- (`EN`) ASCII digit or Eastern Arabic-Indic digit -/
| europeanNumber
/-- (`ES`) European separator: plus and-/
| europeanSeparator
/-- (`ET`) European terminator in a numeric format context, includes currency signs -/
| europeanTerminator
/-- (`AN`) Arabic-Indic digit -/
| arabicNumber
/-- (`CS`) common separator: commas, colons, and slashes -/
| commonSeparator
/-- (`NSM`) nonspacing mark -/
| nonspacingMark
/-- (`BN`) boundary neutral: most format characters, control codes, or noncharacters -/
| boundaryNeutral
/-- (`B`)	paragraph separator, various newline characters -/
| paragraphSeparator
/-- (`S`)	segment separator, various segment-related control codes -/
| segmentSeparator
/-- (`WS`) white spaces -/
| whiteSpace
/-- (`ON`) other neutral: most other symbols and punctuation marks -/
| otherNeutral
/-- (`LRE`) left to right embedding (U+202A: the LR embedding control) -/
| leftToRightEmbedding
/-- (`LRO`)	Left_To_Right_Override	(U+202D: the LR override control) -/
| leftToRightOverride
/-- (`RLE`) right-to-left embedding (U+202B: the RL embedding control) -/
| rightToLeftEmbeding
/-- (`RLO`) right-to-left override (U+202E: the RL override control) -/
| rightToLeftOverride
/-- (`PDF`) pop directional format (U+202C: terminates an embedding or override control) -/
| popDirectionalFormat
/-- (`LRI`) left-to-right isolate (U+2066: the LR isolate control) -/
| leftToRightIsolate
/-- (`RLI`) right-toleft isolate (U+2067: the RL isolate control) -/
| rightToLeftIsolate
/-- (`FSI`)	first strong isolate	U+2068: the first strong isolate control -/
| firstStrongIsolate
/-- (`PDI`) pop directional isolate	U+2069: terminates an isolate control -/
| popDirectionalIsolate
deriving Inhabited, DecidableEq

/-- Bidi class: strong left-to-right (`L`) -/
protected def BidiClass.L := leftToRight
/-- Bidi class: strong right-to-left (`R`) -/
protected def BidiClass.R := rightToLeft
/-- Bidi class: arabic letter (`AL`) -/
protected def BidiClass.AL := arabicLetter
/-- Bidi class: european number (`EN`) -/
protected def BidiClass.EN := europeanNumber
/-- Bidi class: european separator (`ES`) -/
protected def BidiClass.ES := europeanSeparator
/-- Bidi class: european terminator (`ET`) -/
protected def BidiClass.ET := europeanTerminator
/-- Bidi class: arabic number (`AN`) -/
protected def BidiClass.AN := arabicNumber
/-- Bidi class: common separator (`CS`) -/
protected def BidiClass.CS := commonSeparator
/-- Bidi class: nonspacing mark (`NSM`) -/
protected def BidiClass.NSM := nonspacingMark
/-- Bidi class: boundary neutral (`BN`) -/
protected def BidiClass.BN := boundaryNeutral
/-- Bidi class: paragraph separator (`B`) -/
protected def BidiClass.B := paragraphSeparator
/-- Bidi class: segment separator (`S`) -/
protected def BidiClass.S := segmentSeparator
/-- Bidi class: white space (`WS`) -/
protected def BidiClass.WS := whiteSpace
/-- Bidi class: other neutral (`ON`) -/
protected def BidiClass.ON := otherNeutral
/-- Bidi class: left-to-right embedding (`LRE`) -/
protected def BidiClass.LRE := leftToRightEmbedding
/-- Bidi class: left-to-right override (`LRO`) -/
protected def BidiClass.LRO := leftToRightOverride
/-- Bidi class: right-to-left embedding (`RLE`) -/
protected def BidiClass.RLE := rightToLeftEmbeding
/-- Bidi class: right-to-left override (`RLO`) -/
protected def BidiClass.RLO := rightToLeftOverride
/-- Bidi class: pop directional format (`PDF`) -/
protected def BidiClass.PDF := popDirectionalFormat
/-- Bidi class: left-to-right isolate (`LRI`) -/
protected def BidiClass.LRI := leftToRightIsolate
/-- Bidi class: right-to-left isolate (`RLI`) -/
protected def BidiClass.RLI := rightToLeftIsolate
/-- Bidi class: first strong isolate (`FSI`) -/
protected def BidiClass.FSI := firstStrongIsolate
/-- Bidi class: pop directional isolate (`PDI`) -/
protected def BidiClass.PDI := popDirectionalIsolate

/-- String abbreviation for bidi class -/
def BidiClass.toAbbrev : BidiClass → String
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
def BidiClass.ofAbbrev? : String → Option BidiClass
| "L" => some leftToRight
| "R" => some rightToLeft
| "AL" => some arabicLetter
| "EN" => some europeanNumber
| "ES" => some europeanSeparator
| "ET" => some europeanTerminator
| "AN" => some arabicNumber
| "CS" => some commonSeparator
| "NSM" => some nonspacingMark
| "BN" => some boundaryNeutral
| "B" => some paragraphSeparator
| "S" => some segmentSeparator
| "WS" => some whiteSpace
| "ON" => some otherNeutral
| "LRE" => some leftToRightEmbedding
| "LRO" => some leftToRightOverride
| "RLE" => some rightToLeftEmbeding
| "RLO" => some rightToLeftOverride
| "PDF" => some popDirectionalFormat
| "LRI" => some leftToRightIsolate
| "RLI" => some rightToLeftIsolate
| "FSI" => some firstStrongIsolate
| "PDI" => some popDirectionalIsolate
| _ => none

@[inherit_doc BidiClass.ofAbbrev?]
def BidiClass.ofAbbrev! (abbr : String) : BidiClass :=
  match ofAbbrev? abbr with
  | some bc => bc
  | none => panic! "invalid bidi category abbrev"

instance : Repr BidiClass where
  reprPrec bc _ := s!"Unicode.BidiClass.{bc.toAbbrev}"

end Unicode
