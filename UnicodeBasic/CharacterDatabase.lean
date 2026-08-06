/-
Copyright © 2023-2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! # Stream types for Unicode Character Database (UCD) files.

Unicode data files are semicolon `;` (U+003B) separated fields, except for
Unihan files and a few others that are tab (U+0009) separated. White spaces
around field values are not significant. Line comments are prefixed with a
number sign `#` (U+0023).
-/

namespace Unicode

/-- UCD stream type

  Comments and blank lines are omitted in this stream type.
  Use `UCDStreamWithComments` if you need comments.
-/
public structure UCDStream (withComments := false) extends String.Slice where
  /-- `isUnihan` is true if the records are tab separated -/
  isUnihan := false
deriving Inhabited

/-- UCD stream type with comments

  Comments and blank lines are included in this stream type.
  Use `UCDStream` if you do not need comments.
-/
public abbrev UCDStreamWithComments := UCDStream (withComments := true)

namespace UCDStream

/-- Make a `UCDStream` from a string slice -/
public abbrev ofStringSlice (str : String.Slice) (withComments := false) (isUnihan := false) :
    UCDStream withComments := { str with isUnihan}

/-- Make a `UCDStream` from a string -/
public abbrev ofString (str : String) (withComments := false) (isUnihan := false) :
    UCDStream withComments := ofStringSlice str.toSlice withComments isUnihan

/-- Make a `UCDStream` from a substring -/
public abbrev ofSubstring (str : Substring.Raw) (withComments := false) (isUnihan := false) :
    UCDStream withComments := ofStringSlice str.toString.toSlice withComments isUnihan

/-- Make a `UCDStream` from a file -/
public abbrev ofFile (path : System.FilePath) (withComments := false) (isUnihan := false) :
    IO (UCDStream withComments) :=
  ofString (withComments := withComments) (isUnihan := isUnihan) <$> IO.FS.readFile path

/-- Get the next line from the `UCDStream` -/
public def nextLine? (stream : UCDStream withComments) :
    Option (String.Slice × String.Slice × UCDStream withComments) := do
  let line := stream.takeWhile (.!='\n')
  if h : line.rawEndPos < stream.rawEndPos then
    let nextPos := stream.posGT line.rawEndPos h
    let pos := line.find '#'
    let row := line.subslice! line.startPos pos
    let cmt := line.subslice! pos line.endPos
    return (row.toSlice, cmt.toSlice, {stream with toSlice := stream.sliceFrom nextPos})
  else failure

public instance : Std.Stream UCDStream (Array String.Slice) where
  next? stream := do
    let mut row := "".toSlice
    let mut stream := stream
    while row.isEmpty do
      let (row', _, stream') ← stream.nextLine?
      row := row'
      stream := stream'
    let sep := if stream.isUnihan then "\t" else ";"
    let dat : Array String.Slice := row.split sep |>.toArray.map (·.trimAscii)
    return (dat, stream)

public instance : Std.Stream UCDStreamWithComments (Array String.Slice × String.Slice) where
  next? stream := do
    let (row, cmt, stream) ← stream.nextLine?
    let sep := if stream.isUnihan then "\t" else ";"
    let dat : Array String.Slice := row.split sep |>.toArray.map (·.trimAscii)
    return ((dat, cmt), stream)
