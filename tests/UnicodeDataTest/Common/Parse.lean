/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeDataTest.Common.Types
public import UnicodeData.UcdParse

open Unicode

namespace UnicodeDataTest.Common.Parse

public def splitComment (raw : String) : String × Option String := Id.run do
  let body := UCD.stripComment raw
  let tail := String.dropWhile raw fun c => c != '#'
  if tail.isEmpty then
    return (body, none)
  else
    return (body, some <| UCD.trimAsciiString ((tail.drop 1).copy))

public def parseHex! (s : String) : UInt32 :=
  ofHexString! s.toSlice

public def parseNat! (s : String) : Nat :=
  s.toNat!

public def parseNatOrX? (s : String) : Option Nat :=
  if s == "x" then none else some (parseNat! s)

public def parseNatArray (s : String) : Array Nat :=
  let s := UCD.trimAsciiString s
  if s.isEmpty then
    #[]
  else
    s.splitOn " " |>.toArray.filter (· ≠ "") |>.map parseNat!

public def parseOptNatArray (s : String) : Array (Option Nat) :=
  let s := UCD.trimAsciiString s
  if s.isEmpty then
    #[]
  else
    s.splitOn " " |>.toArray.filter (· ≠ "") |>.map parseNatOrX?

public def parseLines {α} (src : String) (f : Nat → String → Option α) : Array α := Id.run do
  let mut out := #[]
  let mut lineNo := 0
  for raw in src.splitOn "\n" do
    lineNo := lineNo + 1
    match f lineNo raw with
    | some row => out := out.push row
    | none => continue
  return out

end UnicodeDataTest.Common.Parse
