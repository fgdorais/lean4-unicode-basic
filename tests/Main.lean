module
import Spec.RunSpec
import UnicodeDataTest.Auxiliary.Test
import UnicodeDataTest.Conformance.Test
import UnicodeTableTest.Spec

public def main (args : List String) : IO UInt32 := do
  Spec.runSpecFromArgsAndReturnExitCode args do
    Spec.describe "UnicodeDataTest" do
      UnicodeDataTest.Auxiliary.spec
      UnicodeDataTest.Conformance.spec

    Spec.describe "UnicodeTableTest" do
      UnicodeTableTest.spec
