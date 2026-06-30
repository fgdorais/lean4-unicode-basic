module
import UnicodeDataTest.Auxiliary.Test
import UnicodeDataTest.Conformance.Test

public def main : IO UInt32 := do
  let aux ← UnicodeDataTest.Auxiliary.run
  let conf ← UnicodeDataTest.Conformance.run
  return if aux == 0 && conf == 0 then 0 else 1
