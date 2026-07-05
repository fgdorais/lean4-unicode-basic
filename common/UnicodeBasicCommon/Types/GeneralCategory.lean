module

/-!
  ## General Category ##
-/

namespace Unicode

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
end Unicode
