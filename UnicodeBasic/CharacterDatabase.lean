/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Unicode

/-- Stream type for Unicode Character Database (UCD) files

  Unicode data files are semicolon `;` (U+003B) separated fields, except for
  Unihan files and a few others that are tab (U+0009) separated. White spaces
  around field values are not significant. Line comments are prefixed with a
  number sign `#` (U+0023).
-/
structure UCDStream extends Substring where
  /-- `isUnihan` is true if the records are tab separated -/
  isUnihan := false
deriving Inhabited

namespace UCDStream

/-- Make a `UCDStream` from a substring -/
def ofSubstring (str : Substring) : UCDStream where
  toSubstring := str

/-- Make a `UCDStream` from a string -/
def ofString (str : String) : UCDStream where
  str := str
  startPos := 0
  stopPos := str.endPos

/-- Make a `UCDStream` from a file -/
def ofFile (path : System.FilePath) : IO UCDStream :=
  ofString <$> IO.FS.readFile path

/-- Get the next line from the `UCDStream`

  Line comments are stripped and blank lines are skipped.
-/
protected partial def nextLine? (stream : UCDStream) : Option (Substring × UCDStream) := do
  if stream.isEmpty then failure else
    let line := stream.trimLeft.takeWhile (.!='\n')
    let nextPos := stream.next line.stopPos
    let line := (line.takeWhile (.!='#')).trimRight
    if line.isEmpty then
      UCDStream.nextLine? {stream with startPos := nextPos}
    else
      return (line, {stream with startPos := nextPos})

/-- Get the next record from the `UCDStream`

  Spaces around field values are trimmed.
-/
protected def next? (stream : UCDStream) : Option (Array Substring × UCDStream) := do
    let sep := if stream.isUnihan then "\t" else ";"
    let mut arr := #[]
    let (line, table) ← stream.nextLine?
    for item in line.splitOn sep do
      arr := arr.push item.trim
    return (arr, table)

instance : Std.Stream UCDStream (Array Substring) where
  next? := UCDStream.next?

end UCDStream

end Unicode
