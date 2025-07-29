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

/-- Coercion from `String` to `Substring`

  This coercion is in Batteries but not in Lean. It is scoped to `Unicode` here to avoid issues in
  low-level packages that don't use Batteries.
-/
scoped instance : Coe String Substring where
  coe := String.toSubstring

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
def ofHexString? (str : Substring) : Option UInt32 := do
  let str := if str.take 2 == "U+" then str.drop 2 else str
  if str.isEmpty || str.bsize > 8 then none else
    let mut val : UInt32 := 0
    for dgt in str do
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
def ofHexString! (str : Substring) : UInt32 :=
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
protected def Sk  : GC := (0x0010000 : UInt32)
protected def So  : GC := (0x0020000 : UInt32)
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

def ofAbbrev? (s : Substring) : Option GC :=
  if s.bsize = 0 || s.bsize > 2 then none else
    match s.get 0 with
    | 'C' =>
      if s.bsize = 1 then some .C else
        match s.get ⟨1⟩ with
        | 'c' => some .Cc
        | 'f' => some .Cf
        | 's' => some .Cs
        | 'o' => some .Co
        | 'n' => some .Cn
        | _ => none
    | 'L' =>
      if s.bsize = 1 then some .L else
        match s.get ⟨1⟩ with
        | 'C' => some .LC
        | 'u' => some .Lu
        | 'l' => some .Ll
        | 't' => some .Lt
        | 'm' => some .Lm
        | 'o' => some .Lo
        | _ => none
    | 'M' =>
      if s.bsize = 1 then some .M else
        match s.get ⟨1⟩ with
        | 'n' => some .Mn
        | 'c' => some .Mc
        | 'e' => some .Me
        | _ => none
    | 'N' =>
      if s.bsize = 1 then some .N else
        match s.get ⟨1⟩ with
        | 'd' => some .Nd
        | 'l' => some .Nl
        | 'o' => some .No
        | _ => none
    | 'P' =>
      if s.bsize = 1 then some .P else
        match s.get ⟨1⟩ with
        | 'G' => some .PG
        | 'Q' => some .PQ
        | 'c' => some .Pc
        | 'd' => some .Pd
        | 's' => some .Ps
        | 'e' => some .Pe
        | 'i' => some .Pi
        | 'f' => some .Pf
        | 'o' => some .Po
        | _ => none
    | 'S' =>
      if s.bsize = 1 then some .S else
        match s.get ⟨1⟩ with
        | 'm' => some .Sm
        | 'c' => some .Sc
        | 'k' => some .Sk
        | 'o' => some .So
        | _ => none
    | 'Z' =>
      if s.bsize = 1 then some .Z else
        match s.get ⟨1⟩ with
        | 's' => some .Zs
        | 'l' => some .Zl
        | 'p' => some .Zp
        | _ => none
    | _ => none

def ofAbbrev! (s : Substring) : GC :=
  match ofAbbrev? s with
  | some c => c
  | none => panic! "invalid general category"

def ofString? (s : Substring) : Option GC := do
  let mut c := .none
  for a in s.splitOn "|" do
    c := c ||| (← GC.ofAbbrev? a.trim)
  return c

def ofString! (s : Substring) : GC :=
  match ofString? s with
  | some c => c
  | none => panic! "invalid general category"

end GC

set_option linter.deprecated false in
@[deprecated Unicode.GC (since := "1.3.0")]
structure GeneralCategory : Type where
  /-- Major general category of a code point -/
  major : MajorGeneralCategory
  /-- Minor general category of a code point -/
  minor : Option (MinorGeneralCategory major)
deriving Inhabited, DecidableEq

set_option linter.deprecated false in section

/-- General category: letter (`L`) -/
@[deprecated Unicode.GC.L (since := "1.3.0")]
protected def GeneralCategory.L  : GeneralCategory := ⟨.letter, none⟩
/-- General category: cased letter (`LC`) -/
@[deprecated Unicode.GC.LC (since := "1.3.0")]
protected def GeneralCategory.LC : GeneralCategory := ⟨_, some .casedLetter⟩
/-- General category: uppercase letter (`Lu`) -/
@[deprecated Unicode.GC.Lu (since := "1.3.0")]
protected def GeneralCategory.Lu : GeneralCategory := ⟨_, some .uppercaseLetter⟩
/-- General category: lowercase letter (`Ll`) -/
@[deprecated Unicode.GC.Ll (since := "1.3.0")]
protected def GeneralCategory.Ll : GeneralCategory := ⟨_, some .lowercaseLetter⟩
/-- General category: titlecase letter (`Lt`) -/
@[deprecated Unicode.GC.Lt (since := "1.3.0")]
protected def GeneralCategory.Lt : GeneralCategory := ⟨_, some .titlecaseLetter⟩
/-- General category: modifier letter (`Lm`) -/
@[deprecated Unicode.GC.Lm (since := "1.3.0")]
protected def GeneralCategory.Lm : GeneralCategory := ⟨_, some .modifierLetter⟩
/-- General category: other letter (`Lo`) -/
@[deprecated Unicode.GC.Lo (since := "1.3.0")]
protected def GeneralCategory.Lo : GeneralCategory := ⟨_, some .otherLetter⟩
/-- General category mark (`M`) -/
@[deprecated Unicode.GC.M (since := "1.3.0")]
protected def GeneralCategory.M  : GeneralCategory := ⟨.mark, none⟩
/-- General category: nonspacing combining mark (`Mn`) -/
@[deprecated Unicode.GC.Mn (since := "1.3.0")]
protected def GeneralCategory.Mn : GeneralCategory := ⟨_, some .nonspacingMark⟩
/-- General category: spacing combining mark (`Mc`) -/
@[deprecated Unicode.GC.Mc (since := "1.3.0")]
protected def GeneralCategory.Mc : GeneralCategory := ⟨_, some .spacingMark⟩
/-- General category: enclosing combining mark (`Me`) -/
@[deprecated Unicode.GC.Me (since := "1.3.0")]
protected def GeneralCategory.Me : GeneralCategory := ⟨_, some .enclosingMark⟩
/-- General category: number (`N`) -/
@[deprecated Unicode.GC.N (since := "1.3.0")]
protected def GeneralCategory.N  : GeneralCategory := ⟨.number, none⟩
/-- General category: decimal digit (`Nd`) -/
@[deprecated Unicode.GC.Nd (since := "1.3.0")]
protected def GeneralCategory.Nd : GeneralCategory := ⟨_, some .decimalNumber⟩
/-- General category: letter number (`Nl`) -/
@[deprecated Unicode.GC.Nl (since := "1.3.0")]
protected def GeneralCategory.Nl : GeneralCategory := ⟨_, some .letterNumber⟩
/-- General category: other number (`No`) -/
@[deprecated Unicode.GC.No (since := "1.3.0")]
protected def GeneralCategory.No : GeneralCategory := ⟨_, some .otherNumber⟩
/-- General category: punctuation (`P`) -/
@[deprecated Unicode.GC.P (since := "1.3.0")]
protected def GeneralCategory.P  : GeneralCategory := ⟨.punctuation, none⟩
/-- General category: connector punctuation (`Pc`) -/
@[deprecated Unicode.GC.Pc (since := "1.3.0")]
protected def GeneralCategory.Pc : GeneralCategory := ⟨_, some .connectorPunctuation⟩
/-- General category: dash punctuation (`Pd`) -/
@[deprecated Unicode.GC.Pd (since := "1.3.0")]
protected def GeneralCategory.Pd : GeneralCategory := ⟨_, some .dashPunctuation⟩
/-- General category: grouping punctuation (`PG`) -/
@[deprecated Unicode.GC.PG (since := "1.3.0")]
protected def GeneralCategory.PG : GeneralCategory := ⟨_, some .groupPunctuation⟩
/-- General category: opening punctuation (`Ps`) -/
@[deprecated Unicode.GC.Ps (since := "1.3.0")]
protected def GeneralCategory.Ps : GeneralCategory := ⟨_, some .openPunctuation⟩
/-- General category: closing punctuation (`Pe`) -/
@[deprecated Unicode.GC.Pe (since := "1.3.0")]
protected def GeneralCategory.Pe : GeneralCategory := ⟨_, some .closePunctuation⟩
/-- General category: quoting punctuation (`PQ`) -/
@[deprecated Unicode.GC.PQ (since := "1.3.0")]
protected def GeneralCategory.PQ : GeneralCategory := ⟨_, some .quotePunctuation⟩
/-- General category: initial punctuation (`Pi`) -/
@[deprecated Unicode.GC.Pi (since := "1.3.0")]
protected def GeneralCategory.Pi : GeneralCategory := ⟨_, some .initialPunctuation⟩
/-- General category: final punctuation (`Pf`) -/
@[deprecated Unicode.GC.Pf (since := "1.3.0")]
protected def GeneralCategory.Pf : GeneralCategory := ⟨_, some .finalPunctuation⟩
/-- General category: other punctuation (`Po`) -/
@[deprecated Unicode.GC.Po (since := "1.3.0")]
protected def GeneralCategory.Po : GeneralCategory := ⟨_, some .otherPunctuation⟩
/-- General category: symbol (`S`) -/
@[deprecated Unicode.GC.S (since := "1.3.0")]
protected def GeneralCategory.S  : GeneralCategory := ⟨.symbol, none⟩
/-- General category: math symbol (`Sm`) -/
@[deprecated Unicode.GC.Sm (since := "1.3.0")]
protected def GeneralCategory.Sm : GeneralCategory := ⟨_, some .mathSymbol⟩
/-- General category: currency symbol (`Sc`) -/
@[deprecated Unicode.GC.Sc (since := "1.3.0")]
protected def GeneralCategory.Sc : GeneralCategory := ⟨_, some .currencySymbol⟩
/-- General category: modifier symbol (`Sk`) -/
@[deprecated Unicode.GC.Sk (since := "1.3.0")]
protected def GeneralCategory.Sk : GeneralCategory := ⟨_, some .modifierSymbol⟩
/-- General category: other symbol (`So`) -/
@[deprecated Unicode.GC.So (since := "1.3.0")]
protected def GeneralCategory.So : GeneralCategory := ⟨_, some .otherSymbol⟩
/-- General category: separator (`Z`) -/
@[deprecated Unicode.GC.Z (since := "1.3.0")]
protected def GeneralCategory.Z  : GeneralCategory := ⟨.separator, none⟩
/-- General category: space separator (`Zs`) -/
@[deprecated Unicode.GC.Zs (since := "1.3.0")]
protected def GeneralCategory.Zs : GeneralCategory := ⟨_, some .spaceSeparator⟩
/-- General category: line separator (`Zl`) -/
@[deprecated Unicode.GC.Zl (since := "1.3.0")]
protected def GeneralCategory.Zl : GeneralCategory := ⟨_, some .lineSeparator⟩
/-- General category: paragraph separator (`Zp`) -/
@[deprecated Unicode.GC.Zp (since := "1.3.0")]
protected def GeneralCategory.Zp : GeneralCategory := ⟨_, some .paragraphSeparator⟩
/-- General category: other (`C`) -/
@[deprecated Unicode.GC.C (since := "1.3.0")]
protected def GeneralCategory.C  : GeneralCategory := ⟨.other, none⟩
/-- General category: control (`Cc`) -/
@[deprecated Unicode.GC.Cc (since := "1.3.0")]
protected def GeneralCategory.Cc : GeneralCategory := ⟨_, some .control⟩
/-- General category: format (`Cf`) -/
@[deprecated Unicode.GC.Cf (since := "1.3.0")]
protected def GeneralCategory.Cf : GeneralCategory := ⟨_, some .format⟩
/-- General category: surrogate (`Cs`) -/
@[deprecated Unicode.GC.Cs (since := "1.3.0")]
protected def GeneralCategory.Cs : GeneralCategory := ⟨_, some .surrogate⟩
/-- General category: private use (`Co`) -/
@[deprecated Unicode.GC.Co (since := "1.3.0")]
protected def GeneralCategory.Co : GeneralCategory := ⟨_, some .privateUse⟩
/-- General category: unassigned (`Cn`) -/
@[deprecated Unicode.GC.Cn (since := "1.3.0")]
protected def GeneralCategory.Cn : GeneralCategory := ⟨_, some .unassigned⟩

/-- String abbreviation for general category -/
@[deprecated Unicode.GC.toAbbrev! (since := "1.3.0")]
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
| ⟨_, some .groupPunctuation⟩ => "PG"
| ⟨_, some .openPunctuation⟩ => "Ps"
| ⟨_, some .closePunctuation⟩ => "Pe"
| ⟨_, some .quotePunctuation⟩ => "PQ"
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
@[deprecated Unicode.GC.ofAbbrev? (since := "1.3.0")]
def GeneralCategory.ofAbbrev? (s : Substring) : Option GeneralCategory :=
  if s.bsize = 0 || s.bsize > 2 then none else
    match s.get 0 with
    | 'C' =>
      if s.bsize = 1 then some ⟨.other, none⟩ else
        match s.get ⟨1⟩ with
        | 'c' => some ⟨_, some .control⟩
        | 'f' => some ⟨_, some .format⟩
        | 's' => some ⟨_, some .surrogate⟩
        | 'o' => some ⟨_, some .privateUse⟩
        | 'n' => some ⟨_, some .unassigned⟩
        | _ => none
    | 'L' =>
      if s.bsize = 1 then some ⟨.letter, none⟩ else
        match s.get ⟨1⟩ with
        | 'C' => some ⟨_, some .casedLetter⟩
        | 'u' => some ⟨_, some .uppercaseLetter⟩
        | 'l' => some ⟨_, some .lowercaseLetter⟩
        | 't' => some ⟨_, some .titlecaseLetter⟩
        | 'm' => some ⟨_, some .modifierLetter⟩
        | 'o' => some ⟨_, some .otherLetter⟩
        | _ => none
    | 'M' =>
      if s.bsize = 1 then some ⟨.mark, none⟩ else
        match s.get ⟨1⟩ with
        | 'n' => some ⟨_, some .nonspacingMark⟩
        | 'c' => some ⟨_, some .spacingMark⟩
        | 'e' => some ⟨_, some .enclosingMark⟩
        | _ => none
    | 'N' =>
      if s.bsize = 1 then some ⟨.number, none⟩ else
        match s.get ⟨1⟩ with
        | 'd' => some ⟨_, some .decimalNumber⟩
        | 'l' => some ⟨_, some .letterNumber⟩
        | 'o' => some ⟨_, some .otherNumber⟩
        | _ => none
    | 'P' =>
      if s.bsize = 1 then some ⟨.punctuation, none⟩ else
        match s.get ⟨1⟩ with
        | 'G' => some ⟨_, some .groupPunctuation⟩
        | 'Q' => some ⟨_, some .quotePunctuation⟩
        | 'c' => some ⟨_, some .connectorPunctuation⟩
        | 'd' => some ⟨_, some .dashPunctuation⟩
        | 's' => some ⟨_, some .openPunctuation⟩
        | 'e' => some ⟨_, some .closePunctuation⟩
        | 'i' => some ⟨_, some .initialPunctuation⟩
        | 'f' => some ⟨_, some .finalPunctuation⟩
        | 'o' => some ⟨_, some .otherPunctuation⟩
        | _ => none
    | 'S' =>
      if s.bsize = 1 then some ⟨.symbol, none⟩ else
        match s.get ⟨1⟩ with
        | 'm' => some ⟨_, some .mathSymbol⟩
        | 'c' => some ⟨_, some .currencySymbol⟩
        | 'k' => some ⟨_, some .modifierSymbol⟩
        | 'o' => some ⟨_, some .otherSymbol⟩
        | _ => none
    | 'Z' =>
      if s.bsize = 1 then some ⟨.separator, none⟩ else
        match s.get ⟨1⟩ with
        | 's' => some ⟨_, some .spaceSeparator⟩
        | 'l' => some ⟨_, some .lineSeparator⟩
        | 'p' => some ⟨_, some .paragraphSeparator⟩
        | _ => none
    | _ => none

@[deprecated Unicode.GC.ofAbbrev! (since := "1.3.0"), inherit_doc GeneralCategory.ofAbbrev?]
def GeneralCategory.ofAbbrev! (s : Substring) : GeneralCategory :=
  match ofAbbrev? s with
  | some gc => gc
  | none => panic! "invalid general category abbreviation"

instance : Repr GeneralCategory where
  reprPrec gc _ := s!"Unicode.GeneralCategory.{gc.toAbbrev}"

@[deprecated some (since := "1.3.0")]
def GeneralCategory.ofGC? (c : GC) : Option GeneralCategory :=
  match GC.reprAux c with
  | [a] => GeneralCategory.ofAbbrev! a
  | _ => none

@[deprecated id (since := "1.3.0")]
def GeneralCategory.ofGC! (c : GC) : GeneralCategory :=
  (ofGC? c).get!

end

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
def BidiClass.ofAbbrev? (abbr : Substring) : Option BidiClass :=
  match abbr.toString with -- TODO: don't use toString
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
def BidiClass.ofAbbrev! (abbr : Substring) : BidiClass :=
  match ofAbbrev? abbr with
  | some bc => bc
  | none => panic! "invalid bidi class abbreviation"

instance : Repr BidiClass where
  reprPrec bc _ := s!"Unicode.BidiClass.{bc.toAbbrev}"

end Unicode
