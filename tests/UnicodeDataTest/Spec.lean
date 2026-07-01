module
import UnicodeDataTest.Auxiliary.Test
import UnicodeDataTest.Conformance.Test

namespace UnicodeDataTest

public def run : IO Bool := do
  let aux ← UnicodeDataTest.Auxiliary.run
  let conf ← UnicodeDataTest.Conformance.run
  return aux && conf == 0

end UnicodeDataTest
