import UnicodeBasic

def Unicode.ExtractedDerivedGeneralCategory.txt := include_str "../data/extracted/DerivedGeneralCategory.txt"

namespace Test.GeneralCategory
open Unicode

structure Data where
  cn : Array (UInt32 × Option UInt32) := #[]
  lu : Array (UInt32 × Option UInt32) := #[]
  ll : Array (UInt32 × Option UInt32) := #[]
  lt : Array (UInt32 × Option UInt32) := #[]
  lm : Array (UInt32 × Option UInt32) := #[]
  lo : Array (UInt32 × Option UInt32) := #[]
  mn : Array (UInt32 × Option UInt32) := #[]
  me : Array (UInt32 × Option UInt32) := #[]
  mc : Array (UInt32 × Option UInt32) := #[]
  nd : Array (UInt32 × Option UInt32) := #[]
  nl : Array (UInt32 × Option UInt32) := #[]
  no : Array (UInt32 × Option UInt32) := #[]
  zs : Array (UInt32 × Option UInt32) := #[]
  zl : Array (UInt32 × Option UInt32) := #[]
  zp : Array (UInt32 × Option UInt32) := #[]
  cc : Array (UInt32 × Option UInt32) := #[]
  cf : Array (UInt32 × Option UInt32) := #[]
  co : Array (UInt32 × Option UInt32) := #[]
  cs : Array (UInt32 × Option UInt32) := #[]
  pd : Array (UInt32 × Option UInt32) := #[]
  ps : Array (UInt32 × Option UInt32) := #[]
  pe : Array (UInt32 × Option UInt32) := #[]
  pc : Array (UInt32 × Option UInt32) := #[]
  po : Array (UInt32 × Option UInt32) := #[]
  sm : Array (UInt32 × Option UInt32) := #[]
  sc : Array (UInt32 × Option UInt32) := #[]
  sk : Array (UInt32 × Option UInt32) := #[]
  so : Array (UInt32 × Option UInt32) := #[]
  pi : Array (UInt32 × Option UInt32) := #[]
  pf : Array (UInt32 × Option UInt32) := #[]

def Data.init : IO Data := do
  let stream := UCDStream.ofString ExtractedDerivedGeneralCategory.txt
  let mut data : Data := {}
  for record in stream do
    let val := match record[0]!.splitOn ".." with
    | [c₀, c₁] => (ofHexString! c₀, some (ofHexString! c₁))
    | [c] => (ofHexString! c, none)
    | _ => panic! "invalid record in DerivedGeneralCategory.txt"
    match record[1]! with
    | "Cn" => data := {data with cn := data.cn.push val}
    | "Lu" => data := {data with lu := data.lu.push val}
    | "Ll" => data := {data with ll := data.ll.push val}
    | "Lt" => data := {data with lt := data.lt.push val}
    | "Lm" => data := {data with lm := data.lm.push val}
    | "Lo" => data := {data with lo := data.lo.push val}
    | "Mn" => data := {data with mn := data.mn.push val}
    | "Me" => data := {data with me := data.me.push val}
    | "Mc" => data := {data with mc := data.mc.push val}
    | "Nd" => data := {data with nd := data.nd.push val}
    | "Nl" => data := {data with nl := data.nl.push val}
    | "No" => data := {data with no := data.no.push val}
    | "Zs" => data := {data with zs := data.zs.push val}
    | "Zl" => data := {data with zl := data.zl.push val}
    | "Zp" => data := {data with zp := data.zp.push val}
    | "Cc" => data := {data with cc := data.cc.push val}
    | "Cf" => data := {data with cf := data.cf.push val}
    | "Co" => data := {data with co := data.co.push val}
    | "Cs" => data := {data with cs := data.cs.push val}
    | "Pd" => data := {data with pd := data.pd.push val}
    | "Ps" => data := {data with ps := data.ps.push val}
    | "Pe" => data := {data with pe := data.pe.push val}
    | "Pc" => data := {data with pc := data.pc.push val}
    | "Po" => data := {data with po := data.po.push val}
    | "Sm" => data := {data with sm := data.sm.push val}
    | "Sc" => data := {data with sc := data.sc.push val}
    | "Sk" => data := {data with sk := data.sk.push val}
    | "So" => data := {data with so := data.so.push val}
    | "Pi" => data := {data with pi := data.pi.push val}
    | "Pf" => data := {data with pf := data.pf.push val}
    | _ => panic! "invalid record in DerivedGeneralCategory.txt"
  return data

@[init Data.init]
def Data.data : Data := {}

def runTest (data : Array (UInt32 × Option UInt32)) (test : UInt32 → Bool) : IO Nat := do
  let mut errors : Nat := 0
  let mut c : UInt32 := 0
  for (start, stop) in data do
    let stop := match stop with
    | some stop => stop
    | none => start
    while c < start do
      if test c then
        errors := errors + 1
      c := c + 1
    while c < stop do
      if !test c then
        errors := errors + 1
      c := c + 1
    if !test c then
      errors := errors + 1
    c := c + 1
  while c <= Unicode.max do
    if test c then
      errors := errors + 1
    c := c + 1
  return errors

unsafe def run : IO Nat := do
  let mut errors := 0
  errors := errors + (← runTest Data.data.cn fun c => GeneralCategory.isCn (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.lu fun c => GeneralCategory.isLu (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.ll fun c => GeneralCategory.isLl (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.lt fun c => GeneralCategory.isLt (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.lm fun c => GeneralCategory.isLm (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.lo fun c => GeneralCategory.isLo (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.mn fun c => GeneralCategory.isMn (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.me fun c => GeneralCategory.isMe (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.mc fun c => GeneralCategory.isMc (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.nd fun c => GeneralCategory.isNd (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.nl fun c => GeneralCategory.isNl (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.no fun c => GeneralCategory.isNo (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.zs fun c => GeneralCategory.isZs (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.zl fun c => GeneralCategory.isZl (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.zp fun c => GeneralCategory.isZp (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.cc fun c => GeneralCategory.isCc (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.cf fun c => GeneralCategory.isCf (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.co fun c => GeneralCategory.isCo (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.cs fun c => GeneralCategory.isCs (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.pd fun c => GeneralCategory.isPd (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.ps fun c => GeneralCategory.isPs (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.pe fun c => GeneralCategory.isPe (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.pc fun c => GeneralCategory.isPc (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.po fun c => GeneralCategory.isPo (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.sm fun c => GeneralCategory.isSm (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.sc fun c => GeneralCategory.isSc (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.sk fun c => GeneralCategory.isSk (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.so fun c => GeneralCategory.isSo (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.pi fun c => GeneralCategory.isPi (Char.mkUnsafe c))
  errors := errors + (← runTest Data.data.pf fun c => GeneralCategory.isPf (Char.mkUnsafe c))
  return errors

end Test.GeneralCategory
