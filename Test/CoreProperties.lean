import UnicodeBasic

def Unicode.DerivedCoreProperties.txt : String := include_str "../data/DerivedCoreProperties.txt"

namespace Test.CoreProperties
open Unicode

structure Data where
  math : Array (UInt32 × Option UInt32) := #[]
  alphabetic : Array (UInt32 × Option UInt32) := #[]
  lowercase : Array (UInt32 × Option UInt32) := #[]
  uppercase : Array (UInt32 × Option UInt32) := #[]
  cased : Array (UInt32 × Option UInt32) := #[]
  caseIgnorable : Array (UInt32 × Option UInt32) := #[]
  whiteSpace : Array (UInt32 × Option UInt32) := #[]

private unsafe def Data.init : IO Data := do
  let mut data : Data := {}
  let stream := UCDStream.ofString DerivedCoreProperties.txt
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.splitOn ".." with
      | [c] => (ofHexString! c, none)
      | [c₀,c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in DerivedCoreProperties.txt"
    match record[1]! with
    | "Math" => data := {data with math := data.math.push val}
    | "Alphabetic" => data := {data with alphabetic := data.alphabetic.push val}
    | "Lowercase" => data := {data with lowercase := data.lowercase.push val}
    | "Uppercase" => data := {data with uppercase := data.uppercase.push val}
    | "Cased" => data := {data with cased := data.cased.push val}
    | "Case_Ignorable" => data := {data with caseIgnorable := data.caseIgnorable.push val}
    | _ => continue
  let stream := UCDStream.ofString PropList.txt
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.splitOn ".." with
      | [c] => (ofHexString! c, none)
      | [c₀,c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in PropList.txt"
    match record[1]! with
    | "White_Space" => data := {data with whiteSpace := data.whiteSpace.push val}
    | _ => continue
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

unsafe abbrev runAlphabetic := runTest Data.data.alphabetic fun c => isAlphabetic (Char.mkUnsafe c)

unsafe abbrev runCased := runTest Data.data.cased fun c => isCased (Char.mkUnsafe c)

unsafe abbrev runCaseIgnorable := runTest Data.data.caseIgnorable fun c => isCaseIgnorable (Char.mkUnsafe c)

unsafe abbrev runLowercase := runTest Data.data.lowercase fun c => isLowercase (Char.mkUnsafe c)

unsafe abbrev runMath := runTest Data.data.math fun c => isMath (Char.mkUnsafe c)

unsafe abbrev runUppercase := runTest Data.data.uppercase fun c => isUppercase (Char.mkUnsafe c)

unsafe abbrev runWhiteSpace := runTest Data.data.whiteSpace fun c => isWhiteSpace (Char.mkUnsafe c)

end Test.CoreProperties
