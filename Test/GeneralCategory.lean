import UnicodeBasic

def Unicode.ExtractedDerivedGeneralCategory.txt := include_str "../data/extracted/DerivedGeneralCategory.txt"

namespace Test.GeneralCategory
open Unicode

structure Data where
  catC  : Array (UInt32 × Option UInt32) := #[]
  catCc : Array (UInt32 × Option UInt32) := #[]
  catCf : Array (UInt32 × Option UInt32) := #[]
  catCn : Array (UInt32 × Option UInt32) := #[]
  catCo : Array (UInt32 × Option UInt32) := #[]
  catCs : Array (UInt32 × Option UInt32) := #[]
  catL  : Array (UInt32 × Option UInt32) := #[]
  catLC : Array (UInt32 × Option UInt32) := #[]
  catLl : Array (UInt32 × Option UInt32) := #[]
  catLm : Array (UInt32 × Option UInt32) := #[]
  catLo : Array (UInt32 × Option UInt32) := #[]
  catLt : Array (UInt32 × Option UInt32) := #[]
  catLu : Array (UInt32 × Option UInt32) := #[]
  catM  : Array (UInt32 × Option UInt32) := #[]
  catMc : Array (UInt32 × Option UInt32) := #[]
  catMe : Array (UInt32 × Option UInt32) := #[]
  catMn : Array (UInt32 × Option UInt32) := #[]
  catN  : Array (UInt32 × Option UInt32) := #[]
  catNd : Array (UInt32 × Option UInt32) := #[]
  catNl : Array (UInt32 × Option UInt32) := #[]
  catNo : Array (UInt32 × Option UInt32) := #[]
  catP  : Array (UInt32 × Option UInt32) := #[]
  catPc : Array (UInt32 × Option UInt32) := #[]
  catPd : Array (UInt32 × Option UInt32) := #[]
  catPe : Array (UInt32 × Option UInt32) := #[]
  catPf : Array (UInt32 × Option UInt32) := #[]
  catPi : Array (UInt32 × Option UInt32) := #[]
  catPo : Array (UInt32 × Option UInt32) := #[]
  catPs : Array (UInt32 × Option UInt32) := #[]
  catS  : Array (UInt32 × Option UInt32) := #[]
  catSc : Array (UInt32 × Option UInt32) := #[]
  catSk : Array (UInt32 × Option UInt32) := #[]
  catSm : Array (UInt32 × Option UInt32) := #[]
  catSo : Array (UInt32 × Option UInt32) := #[]
  catZ  : Array (UInt32 × Option UInt32) := #[]
  catZl : Array (UInt32 × Option UInt32) := #[]
  catZp : Array (UInt32 × Option UInt32) := #[]
  catZs : Array (UInt32 × Option UInt32) := #[]

def Data.init : IO Data := do
  let stream := UCDStream.ofString ExtractedDerivedGeneralCategory.txt
  let mut data : Data := {}
  for record in stream do
    let val := match record[0]!.splitOn ".." with
    | [c₀, c₁] => (ofHexString! c₀, some (ofHexString! c₁))
    | [c] => (ofHexString! c, none)
    | _ => panic! "invalid record in DerivedGeneralCategory.txt"
    match record[1]! with
    | "Cc" => data := {data with catCc := data.catCc.push val}
    | "Cf" => data := {data with catCf := data.catCf.push val}
    | "Cn" => data := {data with catCn := data.catCn.push val}
    | "Co" => data := {data with catCo := data.catCo.push val}
    | "Cs" => data := {data with catCs := data.catCs.push val}
    | "Ll" => data := {data with catLl := data.catLl.push val}
    | "Lm" => data := {data with catLm := data.catLm.push val}
    | "Lo" => data := {data with catLo := data.catLo.push val}
    | "Lt" => data := {data with catLt := data.catLt.push val}
    | "Lu" => data := {data with catLu := data.catLu.push val}
    | "Mc" => data := {data with catMc := data.catMc.push val}
    | "Me" => data := {data with catMe := data.catMe.push val}
    | "Mn" => data := {data with catMn := data.catMn.push val}
    | "Nd" => data := {data with catNd := data.catNd.push val}
    | "Nl" => data := {data with catNl := data.catNl.push val}
    | "No" => data := {data with catNo := data.catNo.push val}
    | "Pc" => data := {data with catPc := data.catPc.push val}
    | "Pd" => data := {data with catPd := data.catPd.push val}
    | "Pe" => data := {data with catPe := data.catPe.push val}
    | "Pi" => data := {data with catPi := data.catPi.push val}
    | "Pf" => data := {data with catPf := data.catPf.push val}
    | "Po" => data := {data with catPo := data.catPo.push val}
    | "Ps" => data := {data with catPs := data.catPs.push val}
    | "Sc" => data := {data with catSc := data.catSc.push val}
    | "Sk" => data := {data with catSk := data.catSk.push val}
    | "Sm" => data := {data with catSm := data.catSm.push val}
    | "So" => data := {data with catSo := data.catSo.push val}
    | "Zl" => data := {data with catZl := data.catZl.push val}
    | "Zp" => data := {data with catZp := data.catZp.push val}
    | "Zs" => data := {data with catZs := data.catZs.push val}
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

unsafe abbrev runCc : IO Nat := runTest Data.data.catCc fun c => GeneralCategory.isCc (Char.mkUnsafe c)
unsafe abbrev runCf : IO Nat := runTest Data.data.catCf fun c => GeneralCategory.isCf (Char.mkUnsafe c)
unsafe abbrev runCn : IO Nat := runTest Data.data.catCn fun c => GeneralCategory.isCn (Char.mkUnsafe c)
unsafe abbrev runCo : IO Nat := runTest Data.data.catCo fun c => GeneralCategory.isCo (Char.mkUnsafe c)
unsafe abbrev runCs : IO Nat := runTest Data.data.catCs fun c => GeneralCategory.isCs (Char.mkUnsafe c)
unsafe abbrev runLl : IO Nat := runTest Data.data.catLl fun c => GeneralCategory.isLl (Char.mkUnsafe c)
unsafe abbrev runLm : IO Nat := runTest Data.data.catLm fun c => GeneralCategory.isLm (Char.mkUnsafe c)
unsafe abbrev runLo : IO Nat := runTest Data.data.catLo fun c => GeneralCategory.isLo (Char.mkUnsafe c)
unsafe abbrev runLt : IO Nat := runTest Data.data.catLt fun c => GeneralCategory.isLt (Char.mkUnsafe c)
unsafe abbrev runLu : IO Nat := runTest Data.data.catLu fun c => GeneralCategory.isLu (Char.mkUnsafe c)
unsafe abbrev runMc : IO Nat := runTest Data.data.catMc fun c => GeneralCategory.isMc (Char.mkUnsafe c)
unsafe abbrev runMe : IO Nat := runTest Data.data.catMe fun c => GeneralCategory.isMe (Char.mkUnsafe c)
unsafe abbrev runMn : IO Nat := runTest Data.data.catMn fun c => GeneralCategory.isMn (Char.mkUnsafe c)
unsafe abbrev runNd : IO Nat := runTest Data.data.catNd fun c => GeneralCategory.isNd (Char.mkUnsafe c)
unsafe abbrev runNl : IO Nat := runTest Data.data.catNl fun c => GeneralCategory.isNl (Char.mkUnsafe c)
unsafe abbrev runNo : IO Nat := runTest Data.data.catNo fun c => GeneralCategory.isNo (Char.mkUnsafe c)
unsafe abbrev runPc : IO Nat := runTest Data.data.catPc fun c => GeneralCategory.isPc (Char.mkUnsafe c)
unsafe abbrev runPd : IO Nat := runTest Data.data.catPd fun c => GeneralCategory.isPd (Char.mkUnsafe c)
unsafe abbrev runPe : IO Nat := runTest Data.data.catPe fun c => GeneralCategory.isPe (Char.mkUnsafe c)
unsafe abbrev runPf : IO Nat := runTest Data.data.catPf fun c => GeneralCategory.isPf (Char.mkUnsafe c)
unsafe abbrev runPi : IO Nat := runTest Data.data.catPi fun c => GeneralCategory.isPi (Char.mkUnsafe c)
unsafe abbrev runPo : IO Nat := runTest Data.data.catPo fun c => GeneralCategory.isPo (Char.mkUnsafe c)
unsafe abbrev runPs : IO Nat := runTest Data.data.catPs fun c => GeneralCategory.isPs (Char.mkUnsafe c)
unsafe abbrev runSc : IO Nat := runTest Data.data.catSc fun c => GeneralCategory.isSc (Char.mkUnsafe c)
unsafe abbrev runSk : IO Nat := runTest Data.data.catSk fun c => GeneralCategory.isSk (Char.mkUnsafe c)
unsafe abbrev runSm : IO Nat := runTest Data.data.catSm fun c => GeneralCategory.isSm (Char.mkUnsafe c)
unsafe abbrev runSo : IO Nat := runTest Data.data.catSo fun c => GeneralCategory.isSo (Char.mkUnsafe c)
unsafe abbrev runZl : IO Nat := runTest Data.data.catZl fun c => GeneralCategory.isZl (Char.mkUnsafe c)
unsafe abbrev runZp : IO Nat := runTest Data.data.catZp fun c => GeneralCategory.isZp (Char.mkUnsafe c)
unsafe abbrev runZs : IO Nat := runTest Data.data.catZs fun c => GeneralCategory.isZs (Char.mkUnsafe c)

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
