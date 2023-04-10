import UnicodeBasic

def Unicode.ExtractedDerivedNumericType.txt := include_str "../data/extracted/DerivedNumericType.txt"

namespace Test.NumericType
open Unicode

structure Data where
  decimal : Array (UInt32 × Option UInt32) := #[]
  digit   : Array (UInt32 × Option UInt32) := #[]
  numeric : Array (UInt32 × Option UInt32) := #[]

def Data.init : IO Data := do
  let stream := UCDStream.ofString ExtractedDerivedNumericType.txt
  let mut data : Data := {}
  for record in stream do
    let val := match record[0]!.splitOn ".." with
    | [c₀, c₁] => (ofHexString! c₀, some (ofHexString! c₁))
    | [c] => (ofHexString! c, none)
    | _ => panic! "invalid record in DerivedNumericType.txt"
    match record[1]! with
    | "Decimal" => data := {data with decimal := data.decimal.push val}
    | "Digit" => data := {data with digit := data.digit.push val}
    | "Numeric" => data := {data with numeric := data.numeric.push val}
    | _ => panic! "invalid record in DerivedNumericType.txt"
  return data

@[init Data.init]
def Data.data : Data := {}

abbrev decimalData := Data.data.decimal
abbrev digitData := Data.data.digit
abbrev numericData := Data.data.numeric

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
  errors := errors + (← runTest decimalData fun c => isDecimal (Char.mkUnsafe c))
  errors := errors + (← runTest digitData fun c => isDigit (Char.mkUnsafe c) && !isDecimal (Char.mkUnsafe c))
  errors := errors + (← runTest numericData fun c => isNumeric (Char.mkUnsafe c) && !isDigit (Char.mkUnsafe c))
  return errors

end Test.NumericType

