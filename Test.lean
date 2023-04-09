import UnicodeBasic
import Test.GeneralCategory
import Test.NumericType

unsafe def main (args : List String) : IO Unit := do
  if args.length == 0 then
    IO.println "No properties to test!"
  else
    for a in args do
      match a with
      | "General_Category" =>
        IO.print "Testing General_Category property ... "
        let errors ← Test.GeneralCategory.run
        IO.println s!"{errors} errors."
      | "Numeric_Type" =>
        IO.print "Testing Numeric_Type property ... "
        let errors ← Test.NumericType.run
        IO.println s!"{errors} errors."
      | _ =>
        IO.println s!"Unrecognized property {a}"
