import UnicodeBasic

def Unicode.ExtractedDerivedGeneralCategory.txt := include_str "../data/extracted/DerivedGeneralCategory.txt"

namespace Test.GeneralCategory
open Unicode

structure Data where
  cc : Array (UInt32 × Option UInt32) := #[]
  cf : Array (UInt32 × Option UInt32) := #[]
  cn : Array (UInt32 × Option UInt32) := #[]
  co : Array (UInt32 × Option UInt32) := #[]
  cs : Array (UInt32 × Option UInt32) := #[]
  ll : Array (UInt32 × Option UInt32) := #[]
  lm : Array (UInt32 × Option UInt32) := #[]
  lo : Array (UInt32 × Option UInt32) := #[]
  lt : Array (UInt32 × Option UInt32) := #[]
  lu : Array (UInt32 × Option UInt32) := #[]
  mc : Array (UInt32 × Option UInt32) := #[]
  me : Array (UInt32 × Option UInt32) := #[]
  mn : Array (UInt32 × Option UInt32) := #[]
  nd : Array (UInt32 × Option UInt32) := #[]
  nl : Array (UInt32 × Option UInt32) := #[]
  no : Array (UInt32 × Option UInt32) := #[]
  pc : Array (UInt32 × Option UInt32) := #[]
  pd : Array (UInt32 × Option UInt32) := #[]
  pe : Array (UInt32 × Option UInt32) := #[]
  pf : Array (UInt32 × Option UInt32) := #[]
  pi : Array (UInt32 × Option UInt32) := #[]
  po : Array (UInt32 × Option UInt32) := #[]
  ps : Array (UInt32 × Option UInt32) := #[]
  sc : Array (UInt32 × Option UInt32) := #[]
  sk : Array (UInt32 × Option UInt32) := #[]
  sm : Array (UInt32 × Option UInt32) := #[]
  so : Array (UInt32 × Option UInt32) := #[]
  zl : Array (UInt32 × Option UInt32) := #[]
  zp : Array (UInt32 × Option UInt32) := #[]
  zs : Array (UInt32 × Option UInt32) := #[]

def Data.init : IO Data := do
  let stream := UCDStream.ofString ExtractedDerivedGeneralCategory.txt
  let mut data : Data := {}
  for record in stream do
    let val := match record[0]!.splitOn ".." with
    | [c₀, c₁] => (ofHexString! c₀, some (ofHexString! c₁))
    | [c] => (ofHexString! c, none)
    | _ => panic! "invalid record in DerivedGeneralCategory.txt"
    match record[1]! with
    | "Cc" => data := {data with cc := data.cc.push val}
    | "Cf" => data := {data with cf := data.cf.push val}
    | "Cn" => data := {data with cn := data.cn.push val}
    | "Co" => data := {data with co := data.co.push val}
    | "Cs" => data := {data with cs := data.cs.push val}
    | "Ll" => data := {data with ll := data.ll.push val}
    | "Lm" => data := {data with lm := data.lm.push val}
    | "Lo" => data := {data with lo := data.lo.push val}
    | "Lt" => data := {data with lt := data.lt.push val}
    | "Lu" => data := {data with lu := data.lu.push val}
    | "Mc" => data := {data with mc := data.mc.push val}
    | "Me" => data := {data with me := data.me.push val}
    | "Mn" => data := {data with mn := data.mn.push val}
    | "Nd" => data := {data with nd := data.nd.push val}
    | "Nl" => data := {data with nl := data.nl.push val}
    | "No" => data := {data with no := data.no.push val}
    | "Pc" => data := {data with pc := data.pc.push val}
    | "Pd" => data := {data with pd := data.pd.push val}
    | "Pe" => data := {data with pe := data.pe.push val}
    | "Pi" => data := {data with pi := data.pi.push val}
    | "Pf" => data := {data with pf := data.pf.push val}
    | "Po" => data := {data with po := data.po.push val}
    | "Ps" => data := {data with ps := data.ps.push val}
    | "Sc" => data := {data with sc := data.sc.push val}
    | "Sk" => data := {data with sk := data.sk.push val}
    | "Sm" => data := {data with sm := data.sm.push val}
    | "So" => data := {data with so := data.so.push val}
    | "Zl" => data := {data with zl := data.zl.push val}
    | "Zp" => data := {data with zp := data.zp.push val}
    | "Zs" => data := {data with zs := data.zs.push val}
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

unsafe abbrev runCc : IO Nat := runTest Data.data.cc fun c => GeneralCategory.isCc (Char.mkUnsafe c)
unsafe abbrev runCf : IO Nat := runTest Data.data.cf fun c => GeneralCategory.isCf (Char.mkUnsafe c)
unsafe abbrev runCn : IO Nat := runTest Data.data.cn fun c => GeneralCategory.isCn (Char.mkUnsafe c)
unsafe abbrev runCo : IO Nat := runTest Data.data.co fun c => GeneralCategory.isCo (Char.mkUnsafe c)
unsafe abbrev runCs : IO Nat := runTest Data.data.cs fun c => GeneralCategory.isCs (Char.mkUnsafe c)
unsafe abbrev runLl : IO Nat := runTest Data.data.ll fun c => GeneralCategory.isLl (Char.mkUnsafe c)
unsafe abbrev runLm : IO Nat := runTest Data.data.lm fun c => GeneralCategory.isLm (Char.mkUnsafe c)
unsafe abbrev runLo : IO Nat := runTest Data.data.lo fun c => GeneralCategory.isLo (Char.mkUnsafe c)
unsafe abbrev runLt : IO Nat := runTest Data.data.lt fun c => GeneralCategory.isLt (Char.mkUnsafe c)
unsafe abbrev runLu : IO Nat := runTest Data.data.lu fun c => GeneralCategory.isLu (Char.mkUnsafe c)
unsafe abbrev runMc : IO Nat := runTest Data.data.mc fun c => GeneralCategory.isMc (Char.mkUnsafe c)
unsafe abbrev runMe : IO Nat := runTest Data.data.me fun c => GeneralCategory.isMe (Char.mkUnsafe c)
unsafe abbrev runMn : IO Nat := runTest Data.data.mn fun c => GeneralCategory.isMn (Char.mkUnsafe c)
unsafe abbrev runNd : IO Nat := runTest Data.data.nd fun c => GeneralCategory.isNd (Char.mkUnsafe c)
unsafe abbrev runNl : IO Nat := runTest Data.data.nl fun c => GeneralCategory.isNl (Char.mkUnsafe c)
unsafe abbrev runNo : IO Nat := runTest Data.data.no fun c => GeneralCategory.isNo (Char.mkUnsafe c)
unsafe abbrev runPc : IO Nat := runTest Data.data.pc fun c => GeneralCategory.isPc (Char.mkUnsafe c)
unsafe abbrev runPd : IO Nat := runTest Data.data.pd fun c => GeneralCategory.isPd (Char.mkUnsafe c)
unsafe abbrev runPe : IO Nat := runTest Data.data.pe fun c => GeneralCategory.isPe (Char.mkUnsafe c)
unsafe abbrev runPf : IO Nat := runTest Data.data.pf fun c => GeneralCategory.isPf (Char.mkUnsafe c)
unsafe abbrev runPi : IO Nat := runTest Data.data.pi fun c => GeneralCategory.isPi (Char.mkUnsafe c)
unsafe abbrev runPo : IO Nat := runTest Data.data.po fun c => GeneralCategory.isPo (Char.mkUnsafe c)
unsafe abbrev runPs : IO Nat := runTest Data.data.ps fun c => GeneralCategory.isPs (Char.mkUnsafe c)
unsafe abbrev runSc : IO Nat := runTest Data.data.sc fun c => GeneralCategory.isSc (Char.mkUnsafe c)
unsafe abbrev runSk : IO Nat := runTest Data.data.sk fun c => GeneralCategory.isSk (Char.mkUnsafe c)
unsafe abbrev runSm : IO Nat := runTest Data.data.sm fun c => GeneralCategory.isSm (Char.mkUnsafe c)
unsafe abbrev runSo : IO Nat := runTest Data.data.so fun c => GeneralCategory.isSo (Char.mkUnsafe c)
unsafe abbrev runZl : IO Nat := runTest Data.data.zl fun c => GeneralCategory.isZl (Char.mkUnsafe c)
unsafe abbrev runZp : IO Nat := runTest Data.data.zp fun c => GeneralCategory.isZp (Char.mkUnsafe c)
unsafe abbrev runZs : IO Nat := runTest Data.data.zs fun c => GeneralCategory.isZs (Char.mkUnsafe c)

unsafe def run : IO Nat := do
  let mut error := 0
  error := error + (← runCc)
  error := error + (← runCf)
  error := error + (← runCn)
  error := error + (← runCo)
  error := error + (← runCs)
  error := error + (← runLl)
  error := error + (← runLm)
  error := error + (← runLo)
  error := error + (← runLt)
  error := error + (← runLu)
  error := error + (← runMc)
  error := error + (← runMe)
  error := error + (← runMn)
  error := error + (← runNd)
  error := error + (← runNl)
  error := error + (← runNo)
  error := error + (← runPc)
  error := error + (← runPd)
  error := error + (← runPe)
  error := error + (← runPf)
  error := error + (← runPi)
  error := error + (← runPo)
  error := error + (← runPs)
  error := error + (← runSc)
  error := error + (← runSk)
  error := error + (← runSm)
  error := error + (← runSo)
  error := error + (← runZl)
  error := error + (← runZp)
  error := error + (← runZs)
  return error

end Test.GeneralCategory
