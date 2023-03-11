/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Unicode

/-- Stream type for data tables

  Unicode data tables are ';'-separated fields. White spaces around field
  values are not significant. Line comments are prefixed with '#'.
-/
structure TableStream extends Substring

namespace TableStream

/-- Make a table stream from a string -/
def ofString (str : String) : TableStream where
  str := str
  startPos := 0
  stopPos := str.endPos

/-- Get the next line from the table

  Skips blank lines and strips line comments.
-/
partial def nextLine? (table : TableStream) : Option (Substring × TableStream) := do
  if table.isEmpty then failure else
    let line := table.trimLeft.takeWhile (.!='\n')
    let nextPos := table.next line.stopPos
    let line := (line.takeWhile (.!='#')).trimRight
    if line.isEmpty then
      nextLine? {table with startPos := nextPos}
    else
      return (line, {table with startPos := nextPos})

instance : Stream TableStream (Array String) where
  next? (table : TableStream) : Option (Array String × TableStream) := do
    let mut arr := #[]
    let (line, table) ← table.nextLine?
    for item in line.splitOn ";" do
      arr := arr.push item.trim.toString
    return (arr, table)

end TableStream

end Unicode
