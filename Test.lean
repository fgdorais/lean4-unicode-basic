import UnicodeBasic
import Test.CoreProperties
import Test.GeneralCategory
import Test.NumericType

unsafe def main (args : List String) : IO Unit := do
  if args.length == 0 then
    IO.println "No properties to test!"
  else
    for a in args do
      match a with
      | "Alphabetic" =>
        IO.print "Testing Alphabetic property ... "
        let errors ← Test.CoreProperties.runAlphabetic
        IO.println s!"{errors} errors."
      | "Cased" =>
        IO.print "Testing Cased property ... "
        let errors ← Test.CoreProperties.runCased
        IO.println s!"{errors} errors."
      | "Case_Ignorable" =>
        IO.print "Testing Case_Ignorable property ... "
        let errors ← Test.CoreProperties.runCaseIgnorable
        IO.println s!"{errors} errors."
      | "General_Category" =>
        IO.print "Testing General_Category property ... "
        let errors ← Test.GeneralCategory.run
        IO.println s!"{errors} errors."
      | "Lowercase" =>
        IO.print "Testing Lowercase property ... "
        let errors ← Test.CoreProperties.runLowercase
        IO.println s!"{errors} errors."
      | "Math" =>
        IO.print "Testing Math property ... "
        let errors ← Test.CoreProperties.runMath
        IO.println s!"{errors} errors."
      | "Numeric_Type" =>
        IO.print "Testing Numeric_Type property ... "
        let errors ← Test.NumericType.run
        IO.println s!"{errors} errors."
      | "Uppercase" =>
        IO.print "Testing Uppercase property ... "
        let errors ← Test.CoreProperties.runUppercase
        IO.println s!"{errors} errors."
      | "White_Space" =>
        IO.print "Testing White_Space property ... "
        let errors ← Test.CoreProperties.runWhiteSpace
        IO.println s!"{errors} errors."
      | _ =>
        IO.println s!"Unrecognized property {a}"
