/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import Std.Data.HashMap

/-- Low-level conversion from `UInt32` to `Char` (*unsafe*)

  This function translates to a no-op in the compiler. However, it does not
  check whether the `UInt32` code is a valid `Char` value. Only use where it's
  known for external reasons that the code is valid. -/
public protected unsafe def Char.mkUnsafe : UInt32 → Char := unsafeCast

namespace Unicode

/-- Maximum valid code point value -/
@[simp, grind =]
public protected abbrev max : UInt32 := 0x10FFFF

/-- Minimum high surrogate code point -/
@[simp, grind =]
public protected abbrev minHighSurrogate : UInt32 := 0xD800

/-- Maximum high surrogate code point -/
@[simp, grind =]
public protected abbrev maxHighSurrogate : UInt32 := 0xDBFF

/-- Minimum low surrogate code point -/
@[simp, grind =]
public protected abbrev minLowSurrogate : UInt32 := 0xDC00

/-- Maximum low surrogate code point -/
@[simp, grind =]
public protected abbrev maxLowSurrogate : UInt32 := 0xDFFF

/-- Minimum surrogate code point -/
@[simp, grind =]
public protected abbrev minSurrogate : UInt32 := Unicode.minHighSurrogate

/-- Minimum surrogate code point -/
@[simp, grind =]
public protected abbrev maxSurrogate : UInt32 := Unicode.maxLowSurrogate

/-- Raw hexadecimal string representation of a code point

  Same as `toHexString` but without the `U+` prefix. -/
public def toHexStringRaw (code : UInt32) : String := Id.run do
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
public def toHexString (code : UInt32) : String :=
  "U+" ++ toHexStringRaw code

/-- Get code point from hexadecimal string representation

  For convenience, the `U+` prefix may be omitted and lowercase hexadecimal
  digits are accepted.
-/
public def ofHexString? (str : String.Slice) : Option UInt32 := do
  let str := if str.take 2 == "U+" then str.drop 2 else str
  if str.isEmpty || str.utf8ByteSize > 8 then none else
    let mut val : UInt32 := 0
    for dgt in str.chars do
      val := (val <<< 4) + (← hexValue? dgt)
    some val

where

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
public def ofHexString! (str : String.Slice) : UInt32 :=
  match ofHexString? str with
  | some val => val
  | none => panic! "invalid unicode hexadecimal string representation"

/-!
  ## General Category ##
-/

/-- General category (GC)

  Unicode property: `General_Category` -/
@[expose]
public def GC := UInt32 deriving DecidableEq, Inhabited

namespace GC

public instance : OrOp GC := inferInstanceAs (OrOp UInt32)

public instance : AndOp GC := inferInstanceAs (AndOp UInt32)

public instance : Complement GC where
  complement x := UInt32.xor x 0x3FFFFFFF

public instance : HasSubset GC where
  Subset x y := x &&& y == x

public instance (x y : GC) : Decidable (x ⊆ y) := inferInstanceAs (Decidable (_ == _))

public protected abbrev none : GC := (0x00000000 : UInt32)
public protected abbrev univ : GC := (0x3FFFFFFF : UInt32)

public protected abbrev Lu  : GC := (0x00000001 : UInt32)
public protected abbrev Ll  : GC := (0x00000002 : UInt32)
public protected abbrev Lt  : GC := (0x00000004 : UInt32)
public protected abbrev Lm  : GC := (0x00000008 : UInt32)
public protected abbrev Lo  : GC := (0x00000010 : UInt32)
public protected abbrev LC  : GC := .Lu ||| .Ll ||| .Lt
public protected abbrev L   : GC := .Lu ||| .Ll ||| .Lt ||| .Lm ||| .Lo

public protected abbrev Mn  : GC := (0x00000020 : UInt32)
public protected abbrev Mc  : GC := (0x00000040 : UInt32)
public protected abbrev Me  : GC := (0x00000080 : UInt32)
public protected abbrev M   : GC := .Mn ||| .Mc ||| .Me

public protected abbrev Nd  : GC := (0x00000100 : UInt32)
public protected abbrev Nl  : GC := (0x00000200 : UInt32)
public protected abbrev No  : GC := (0x00000400 : UInt32)
public protected abbrev N   : GC := .Nd ||| .Nl ||| .No

public protected abbrev Pc  : GC := (0x00000800 : UInt32)
public protected abbrev Pd  : GC := (0x00001000 : UInt32)
public protected abbrev Ps  : GC := (0x00002000 : UInt32)
public protected abbrev Pe  : GC := (0x00004000 : UInt32)
public protected abbrev Pi  : GC := (0x00008000 : UInt32)
public protected abbrev Pf  : GC := (0x00010000 : UInt32)
public protected abbrev Po  : GC := (0x00020000 : UInt32)
public protected abbrev PG  : GC := .Ps ||| .Pe
public protected abbrev PQ  : GC := .Pi ||| .Pf
public protected abbrev P   : GC := .Pc ||| .Pd ||| .Ps ||| .Pe ||| .Pi ||| .Pf ||| .Po

public protected abbrev Sm  : GC := (0x00040000 : UInt32)
public protected abbrev Sc  : GC := (0x00080000 : UInt32)
public protected abbrev Sk  : GC := (0x00100000 : UInt32)
public protected abbrev So  : GC := (0x00200000 : UInt32)
public protected abbrev S   : GC := .Sm ||| .Sc ||| .Sk ||| .So

public protected abbrev Zs  : GC := (0x00400000 : UInt32)
public protected abbrev Zl  : GC := (0x00800000 : UInt32)
public protected abbrev Zp  : GC := (0x01000000 : UInt32)
public protected abbrev Z   : GC := .Zs ||| .Zl ||| .Zp

public protected abbrev Cc  : GC := (0x02000000 : UInt32)
public protected abbrev Cf  : GC := (0x04000000 : UInt32)
public protected abbrev Cs  : GC := (0x08000000 : UInt32)
public protected abbrev Co  : GC := (0x10000000 : UInt32)
public protected abbrev Cn  : GC := (0x20000000 : UInt32)
public protected abbrev C   : GC := .Cc ||| .Cf ||| .Cs ||| .Co ||| .Cn

def reprAux (x : GC) (extra := false) : List String := Id.run do
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
public def toAbbrev! (x : GC) : String :=
  match reprAux x true with
  | [a] => a
  | _ => panic! "invalid general category"

open Std.Format Repr in
public def reprPrec (x : GC) := addAppParen (group (joinSep (reprAux x |>.map (text "Unicode.GC." ++ text ·)) (text " |||" ++ line)) .fill)
public instance : Repr GC where reprPrec

public def toString (x : GC) := " | ".intercalate (reprAux x)
public instance : ToString GC where toString

public def ofAbbrev? (s : String.Slice) : Option GC :=
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

public def ofAbbrev! (s : String.Slice) : GC :=
  match ofAbbrev? s with
  | .some c => c
  | none => panic! "invalid general category"

public def ofString? (s : String.Slice) : Option GC := do
  let mut c := .none
  for a in s.split "|" do
    c := c ||| (← GC.ofAbbrev? a.trimAscii)
  return c

public def ofString! (s : String.Slice) : GC :=
  match ofString? s with
  | .some c => c
  | none => panic! "invalid general category"

end GC

/-!
  ## Numeric Type and Value ##
-/

/-- Unicode numeric type

  Unicode properties: `Numeric_Type`, `Numeric_Value` -/
public inductive NumericType
/-- Decimal digit type and value -/
| public decimal (value : Fin 10) : NumericType
/-- Digit type and value -/
| public digit (value : Fin 10) : NumericType
/-- Numeric type and value -/
| public numeric (num : Int) (den : Option Nat) : NumericType
deriving Inhabited, DecidableEq, Repr

/-- Decimal digit type

  The character is part of a sequence of contiguous code points representing
  decimal digits 0 through 9.

  Unicode property: `Numeric_Type`
-/
public def NumericType.isDecimal : NumericType → Bool
| decimal _ => true
| _ => false

/-- Digit type

  The character represents a decimal digit 0 through 9.

  Unicode property: `Numeric_Type`
-/
public def NumericType.isDigit : NumericType → Bool
| decimal _ => true
| digit _ => true
| _ => false

/-- Get the value of a numeric type

  Returns either an integer value or a numerator-denominator pair representing
  a rational value.

  Unicode property: `Numeric_Value`
-/
@[expose]
public def NumericType.value : NumericType → Int ⊕ Int × Nat
| decimal n => .inl n
| digit n => .inl n
| numeric n none => .inl n
| numeric n (some d) => .inr (n, d)

/-!
  ## Decomposition Mapping ##
-/

/-- Compatibility format tag

  Unicode properties: `Decomposition_Type`, `Decomposition_Mapping` -/
public inductive CompatibilityTag
/-- Font variant -/
| public font
/-- No-break version of a space or hyphen -/
| public noBreak
/-- Initial presentation form (Arabic) -/
| public initial
/-- Medial presentation form (Arabic) -/
| public medial
/-- Final presentation form (Arabic) -/
| public final
/-- Isolated presentation form (Arabic) -/
| public isolated
/-- Encircled form -/
| public circle
/-- Superscript form -/
| public super
/-- Subscript form -/
| public sub
/-- Vertical layout presentation form -/
| public vertical
/-- Wide (or zenkaku) compatibility character -/
| public wide
/-- Narrow (or hankaku) compatibility character -/
| public narrow
/-- Small variant form (CNS compatibility) -/
| public small
/-- CJK squared font variant -/
| public square
/-- Vulgar fraction form -/
| public fraction
/-- Otherwise unspecified compatibility character -/
| public compat
deriving Inhabited, DecidableEq, Repr

public instance : ToString CompatibilityTag where
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
public structure DecompositionMapping where
  /-- Compatibility format tag -/
  public tag : Option CompatibilityTag
  /-- Decomposition mapping -/
  public mapping : List Char
deriving Inhabited, DecidableEq, Repr

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


/-- Grapheme cluster break property

  Unicode property: `Grapheme_Cluster_Break` -/
public inductive GraphemeClusterBreak
| public other
| public control
| public cr
| public extend
| public lf
| public spacingMark
| public prepend
| public regionalIndicator
| public l
| public v
| public t
| public lv
| public lvt
| public zwj
deriving Inhabited, DecidableEq, Repr

public instance : ToString GraphemeClusterBreak where
  toString
  | .other => "Other"
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

public def GraphemeClusterBreak.ofAbbrev? (abbr : String.Slice) : Option GraphemeClusterBreak :=
  if abbr == "XX" || abbr == "Other" then some other
  else if abbr == "CN" || abbr == "Control" then some control
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

@[inherit_doc GraphemeClusterBreak.ofAbbrev?]
public def GraphemeClusterBreak.ofAbbrev! (abbr : String.Slice) : GraphemeClusterBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid grapheme cluster break abbreviation {abbr.copy}"


/-- Word break property

  Unicode property: `Word_Break` -/
public inductive WordBreak
| public other
| public doubleQuote
| public singleQuote
| public hebrewLetter
| public cr
| public lf
| public newline
| public extend
| public regionalIndicator
| public katakana
| public aLetter
| public midLetter
| public midNum
| public midNumLet
| public numeric
| public extendNumLet
| public wSegSpace
| public zwj
| public format
deriving Inhabited, DecidableEq, Repr

public instance : ToString WordBreak where
  toString
  | .other => "Other"
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

public def WordBreak.ofAbbrev? (abbr : String.Slice) : Option WordBreak :=
  if abbr == "XX" || abbr == "Other" then some other
  else if abbr == "DQ" || abbr == "Double_Quote" then some doubleQuote
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

@[inherit_doc WordBreak.ofAbbrev?]
public def WordBreak.ofAbbrev! (abbr : String.Slice) : WordBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid word break abbreviation {abbr.copy}"


/-- Sentence break property

  Unicode property: `Sentence_Break` -/
public inductive SentenceBreak
| public other
| public aTerm
| public cr
| public close
| public extend
| public format
| public lf
| public lower
| public numeric
| public oLetter
| public sContinue
| public sTerm
| public sep
| public sp
| public upper
deriving Inhabited, DecidableEq, Repr

public def SentenceBreak.ofAbbrev? (abbr : String.Slice) : Option SentenceBreak :=
  if abbr == "XX" || abbr == "Other" then some other
  else if abbr == "AT" || abbr == "ATerm" then some aTerm
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
public def SentenceBreak.ofAbbrev! (abbr : String.Slice) : SentenceBreak :=
  match ofAbbrev? abbr with
  | some b => b
  | none => panic! s!"invalid sentence break abbreviation {abbr.copy}"


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

/-!
  ## Scripts ##
-/

/-- Check if valid script identifier -/
@[inline]
public def Script.isValid (c : UInt32) : Bool :=
  let c0 := (c >>> 24).toUInt8
  let c1 := (c >>> 16).toUInt8
  let c2 := (c >>> 8).toUInt8
  let c3 := c.toUInt8
  (c0 ≤ 'Z'.toUInt8 && 'A'.toUInt8 ≤ c0)
    && (c1 ≤ 'z'.toUInt8 && 'a'.toUInt8 ≤ c1)
      && (c2 ≤ 'z'.toUInt8 && 'a'.toUInt8 ≤ c2)
        && (c3 ≤ 'z'.toUInt8 && 'a'.toUInt8 ≤ c3)

/-- Script identifier type -/
public structure Script where
  public code : UInt32
  public is_valid : Script.isValid code
deriving DecidableEq, Hashable

namespace Script

/-- Default value is `Zzzz` (`Unknown`) -/
public instance : Inhabited Script where
  default := {
    code := (((('Z'.val <<< 8 ||| 'z'.val) <<< 8) ||| 'z'.val) <<< 8) ||| 'z'.val
    is_valid := by decide
  }

/-- String abbreviation of script -/
@[extern "unicode_script_to_abbrev"]
public def toAbbrev : Script → String
  | ⟨c, _⟩ =>
    let c0 := Char.ofUInt8 (c >>> 24).toUInt8
    let c1 := Char.ofUInt8 (c >>> 16).toUInt8
    let c2 := Char.ofUInt8 (c >>> 8).toUInt8
    let c3 := Char.ofUInt8 c.toUInt8
    String.ofList [c0, c1, c2, c3]

@[extern "unicode_script_of_abbrev"]
opaque ofAbbrevAux (abbr : String) : UInt32

/-- Get script from abbreviation -/
public def ofAbbrev? (abbr : String.Slice) : Option Script :=
  if abbr.utf8ByteSize = 4 then
    let code := ofAbbrevAux abbr.toString
    if h : Script.isValid code then
      some ⟨code, h⟩
    else
      none
  else
    none

@[inline, inherit_doc ofAbbrev?]
public def ofAbbrev! (abbr : String.Slice) : Script := ofAbbrev? abbr |>.get!

end Script
