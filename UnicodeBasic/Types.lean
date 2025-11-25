/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-- Low-level conversion from `UInt32` to `Char` (*unsafe*)

  This function translates to a no-op in the compiler. However, it does not
  check whether the `UInt32` code is a valid `Char` value. Only use where it's
  known for external reasons that the code is valid. -/
protected unsafe def Char.mkUnsafe : UInt32 → Char := unsafeCast

namespace Unicode

-- forward-port: lean4#11341
/-- Coercion from `String` to `String.Slice` -/
scoped instance : Coe String String.Slice where
  coe := String.toSlice

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
  return String.ofList dgts

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
def ofHexString? (str : String.Slice) : Option UInt32 := do
  let str := if str.take 2 == "U+" then str.drop 2 else str
  if str.isEmpty || str.utf8ByteSize > 8 then none else
    let mut val : UInt32 := 0
    for dgt in str.chars do
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
def ofHexString! (str : String.Slice) : UInt32 :=
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
/-- (`PG`) grouping punctuation mark (derived from `Ps | Pe`) -/
| groupPunctuation : MinorGeneralCategory .punctuation
/-- (`Ps`) opening punctuation mark (of a pair) -/
| openPunctuation : MinorGeneralCategory .punctuation
/-- (`Pe`) closing punctuation mark (of a pair) -/
| closePunctuation : MinorGeneralCategory .punctuation
/-- (`PQ`) quoting punctuation mark (derived from `Pi | Pf`) -/
| quotePunctuation : MinorGeneralCategory .punctuation
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

/-- General category (GC)

  Unicode property: `General_Category` -/
def GC := UInt32 deriving DecidableEq, Inhabited

namespace GC

instance : OrOp GC := inferInstanceAs (OrOp UInt32)

instance : AndOp GC := inferInstanceAs (AndOp UInt32)

instance : Complement GC where
  complement x := UInt32.xor x 0x3FFFFFFF

instance : HasSubset GC where
  Subset x y := x &&& y == x

instance (x y : GC) : Decidable (x ⊆ y) := inferInstanceAs (Decidable (_ == _))

protected def none : GC := (0x00000000 : UInt32)
protected def univ : GC := (0x3FFFFFFF : UInt32)

protected def Lu  : GC := (0x00000001 : UInt32)
protected def Ll  : GC := (0x00000002 : UInt32)
protected def Lt  : GC := (0x00000004 : UInt32)
protected def Lm  : GC := (0x00000008 : UInt32)
protected def Lo  : GC := (0x00000010 : UInt32)
protected def LC  : GC := .Lu ||| .Ll ||| .Lt
protected def L   : GC := .Lu ||| .Ll ||| .Lt ||| .Lm ||| .Lo

protected def Mn  : GC := (0x00000020 : UInt32)
protected def Mc  : GC := (0x00000040 : UInt32)
protected def Me  : GC := (0x00000080 : UInt32)
protected def M   : GC := .Mn ||| .Mc ||| .Me

protected def Nd  : GC := (0x00000100 : UInt32)
protected def Nl  : GC := (0x00000200 : UInt32)
protected def No  : GC := (0x00000400 : UInt32)
protected def N   : GC := .Nd ||| .Nl ||| .No

protected def Pc  : GC := (0x00000800 : UInt32)
protected def Pd  : GC := (0x00001000 : UInt32)
protected def Ps  : GC := (0x00002000 : UInt32)
protected def Pe  : GC := (0x00004000 : UInt32)
protected def Pi  : GC := (0x00008000 : UInt32)
protected def Pf  : GC := (0x00010000 : UInt32)
protected def Po  : GC := (0x00020000 : UInt32)
protected def PG  : GC := .Ps ||| .Pe
protected def PQ  : GC := .Pi ||| .Pf
protected def P   : GC := .Pc ||| .Pd ||| .Ps ||| .Pe ||| .Pi ||| .Pf ||| .Po

protected def Sm  : GC := (0x00040000 : UInt32)
protected def Sc  : GC := (0x00080000 : UInt32)
protected def Sk  : GC := (0x00100000 : UInt32)
protected def So  : GC := (0x00200000 : UInt32)
protected def S   : GC := .Sm ||| .Sc ||| .Sk ||| .So

protected def Zs  : GC := (0x00400000 : UInt32)
protected def Zl  : GC := (0x00800000 : UInt32)
protected def Zp  : GC := (0x01000000 : UInt32)
protected def Z   : GC := .Zs ||| .Zl ||| .Zp

protected def Cc  : GC := (0x02000000 : UInt32)
protected def Cf  : GC := (0x04000000 : UInt32)
protected def Cs  : GC := (0x08000000 : UInt32)
protected def Co  : GC := (0x10000000 : UInt32)
protected def Cn  : GC := (0x20000000 : UInt32)
protected def C   : GC := .Cc ||| .Cf ||| .Cs ||| .Co ||| .Cn

def mk : (major : MajorGeneralCategory) → Option (MinorGeneralCategory major) → GC
| .letter, none => .L
| _, some .casedLetter => .LC
| _, some .uppercaseLetter => .Lu
| _, some .lowercaseLetter => .Ll
| _, some .titlecaseLetter => .Lt
| _, some .modifierLetter => .Lm
| _, some .otherLetter => .Lo
| .mark, none => .M
| _, some .nonspacingMark => .Mn
| _, some .spacingMark => .Mc
| _, some .enclosingMark => .Me
| .number, none => .N
| _, some .decimalNumber => .Nd
| _, some .letterNumber => .Nl
| _, some .otherNumber => .No
| .punctuation, none => .P
| _, some .connectorPunctuation => .Pc
| _, some .dashPunctuation => .Pd
| _, some .groupPunctuation => .PG
| _, some .openPunctuation => .Ps
| _, some .closePunctuation => .Pe
| _, some .quotePunctuation => .PQ
| _, some .initialPunctuation => .Pi
| _, some .finalPunctuation => .Pf
| _, some .otherPunctuation => .Po
| .symbol, none => .S
| _, some .mathSymbol => .Sm
| _, some .currencySymbol => .Sc
| _, some .modifierSymbol => .Sk
| _, some .otherSymbol => .So
| .separator, none => .Z
| _, some .spaceSeparator => .Zs
| _, some .lineSeparator => .Zl
| _, some .paragraphSeparator => .Zp
| .other, none => .C
| _, some .control => .Cc
| _, some .format => .Cf
| _, some .surrogate => .Cs
| _, some .privateUse => .Co
| _, some .unassigned => .Cn

private def reprAux (x : GC) (extra := false) : List String := Id.run do
  let mut c := #[]
  if .L ⊆ x then
    c := c.push "L"
  else
    if .LC ⊆ x then
      c := c.push "LC"
    else
      if .Lu ⊆ x then
        c := c.push "Lu"
      if .Ll ⊆ x then
        c := c.push "Ll"
      if .Lt ⊆ x then
        c := c.push "Lt"
    if .Lm ⊆ x then
      c := c.push "Lm"
    if .Lo ⊆ x then
      c := c.push "Lo"
  if .M ⊆ x then
    c := c.push "M"
  else
    if .Mn ⊆ x then
      c := c.push "Mn"
    if .Mc ⊆ x then
      c := c.push "Mc"
    if .Me ⊆ x then
      c := c.push "Me"
  if .N ⊆ x then
    c := c.push "N"
  else
    if .Nd ⊆ x then
      c := c.push "Nd"
    if .Nl ⊆ x then
      c := c.push "Nl"
    if .No ⊆ x then
      c := c.push "No"
  if .P ⊆ x then
    c := c.push "P"
  else
    if extra && .PG ⊆ x then
      c := c.push "PG"
    else
      if .Ps ⊆ x then
        c := c.push "Ps"
      if .Pe ⊆ x then
        c := c.push "Pe"
    if extra && .PQ ⊆ x then
      c := c.push "PQ"
    else
      if .Pi ⊆ x then
        c := c.push "Pi"
      if .Pf ⊆ x then
        c := c.push "Pf"
    if .Pc ⊆ x then
      c := c.push "Pc"
    if .Pd ⊆ x then
      c := c.push "Pd"
    if .Po ⊆ x then
      c := c.push "Po"
  if .S ⊆ x then
    c := c.push "S"
  else
    if .Sm ⊆ x then
      c := c.push "Sm"
    if .Sc ⊆ x then
      c := c.push "Sc"
    if .Sk ⊆ x then
      c := c.push "Sk"
    if .So ⊆ x then
      c := c.push "So"
  if .Z ⊆ x then
    c := c.push "Z"
  else
    if .Zs ⊆ x then
      c := c.push "Zs"
    if .Zl ⊆ x then
      c := c.push "Zl"
    if .Zp ⊆ x then
      c := c.push "Zp"
  if .C ⊆ x then
    c := c.push "C"
  else
    if .Cc ⊆ x then
      c := c.push "Cc"
    if .Cf ⊆ x then
      c := c.push "Cf"
    if .Cs ⊆ x then
      c := c.push "Cs"
    if .Co ⊆ x then
      c := c.push "Co"
    if .Cn ⊆ x then
      c := c.push "Cn"
  return c.toList

@[inline]
def toAbbrev! (x : GC) : String :=
  match reprAux x true with
  | [a] => a
  | _ => panic! "invalid general category"

open Std.Format Repr in instance : Repr GC where
  reprPrec x := addAppParen (group (joinSep (reprAux x |>.map (text "Unicode.GC." ++ text ·)) (text " |||" ++ line)) .fill)

instance : ToString GC where
  toString x := " | ".intercalate (reprAux x)

def ofAbbrev? (s : String.Slice) : Option GC :=
  match s.chars.take 3 |>.toList with
  | ['C'] => some .C
  | ['C', 'c'] => some .Cc
  | ['C', 'f'] => some .Cf
  | ['C', 's'] => some .Cs
  | ['C', 'o'] => some .Co
  | ['C', 'n'] => some .Cn
  | ['L'] => some .L
  | ['L', 'C'] => some .LC
  | ['L', 'u'] => some .Lu
  | ['L', 'l'] => some .Ll
  | ['L', 't'] => some .Lt
  | ['L', 'm'] => some .Lm
  | ['L', 'o'] => some .Lo
  | ['M'] => some .M
  | ['M', 'n'] => some .Mn
  | ['M', 'c'] => some .Mc
  | ['M', 'e'] => some .Me
  | ['N'] => some .N
  | ['N', 'd'] => some .Nd
  | ['N', 'l'] => some .Nl
  | ['N', 'o'] => some .No
  | ['P'] => some .P
  | ['P', 'G'] => some .PG
  | ['P', 'Q'] => some .PQ
  | ['P', 'c'] => some .Pc
  | ['P', 'd'] => some .Pd
  | ['P', 's'] => some .Ps
  | ['P', 'e'] => some .Pe
  | ['P', 'i'] => some .Pi
  | ['P', 'f'] => some .Pf
  | ['P', 'o'] => some .Po
  | ['S'] => some .S
  | ['S', 'm'] => some .Sm
  | ['S', 'c'] => some .Sc
  | ['S', 'k'] => some .Sk
  | ['S', 'o'] => some .So
  | ['Z'] => some .Z
  | ['Z', 's'] => some .Zs
  | ['Z', 'l'] => some .Zl
  | ['Z', 'p'] => some .Zp
  | _ => none

def ofAbbrev! (s : String.Slice) : GC :=
  match ofAbbrev? s with
  | some c => c
  | none => panic! "invalid general category"

def ofString? (s : String.Slice) : Option GC := do
  let mut c := .none
  for a in s.split "|" do
    c := c ||| (← GC.ofAbbrev? a.trimAscii)
  return c

def ofString! (s : String.Slice) : GC :=
  match ofString? s with
  | some c => c
  | none => panic! "invalid general category"

end GC

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

  The character represents a decimal digit 0 through 9.

  Unicode property: `Numeric_Type`
-/
def NumericType.isDigit : NumericType → Bool
| decimal _ => true
| digit _ => true
| _ => false

/-- Get the value of a numeric type

  Returns either an integer value or a numerator-denominator pair representing
  a rational value.

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
deriving Inhabited, DecidableEq, Repr

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
deriving Inhabited, DecidableEq, Repr

/-!
  ## Bidirectional Class ##
-/

/-- Bidirectional class

  Unicode property: `Bidi_Class` -/
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
/-- (`FSI`)	first strong isolate (U+2068: the first strong isolate control) -/
| firstStrongIsolate
/-- (`PDI`) pop directional isolate (U+2069: terminates an isolate control) -/
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
def BidiClass.ofAbbrev? (abbr : String.Slice) : Option BidiClass :=
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
def BidiClass.ofAbbrev! (abbr : String.Slice) : BidiClass :=
  match ofAbbrev? abbr with
  | some bc => bc
  | none => panic! "invalid bidi class abbreviation"

instance : Repr BidiClass where
  reprPrec bc _ := s!"Unicode.BidiClass.{bc.toAbbrev}"

end Unicode
