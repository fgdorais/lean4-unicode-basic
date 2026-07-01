/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types

namespace Unicode

/-- Paragraph direction used for bidi resolution. -/
public inductive BidiParagraphDirection where
  | ltr
  | rtl
  | autoLtr
deriving Inhabited, DecidableEq, Repr

public instance : ToString BidiParagraphDirection where
  toString
  | .ltr => "ltr"
  | .rtl => "rtl"
  | .autoLtr => "autoLtr"

/-- Result of a bidi resolution query. -/
public structure BidiResolution where
  paragraphLevel : Nat
  resolvedLevels : Array (Option Nat)
  visualOrder : Array Nat
deriving Inhabited, DecidableEq, Repr

namespace CLib

@[extern "unicode_bidi_query_case"]
protected opaque queryCase (text : Array UInt32) (paragraphDirection : UInt32) (fileFormat : UInt32) : String

end CLib

private def paragraphDirectionCode : BidiParagraphDirection → UInt32
  | .ltr => 0
  | .rtl => 1
  | .autoLtr => 2

private def encodeBidiClass : BidiClass → UInt32
  | .leftToRight => 2
  | .otherNeutral => 3
  | .rightToLeft => 4
  | .europeanNumber => 5
  | .europeanSeparator => 6
  | .europeanTerminator => 7
  | .arabicNumber => 8
  | .commonSeparator => 9
  | .paragraphSeparator => 10
  | .segmentSeparator => 11
  | .whiteSpace => 12
  | .arabicLetter => 13
  | .nonspacingMark => 14
  | .boundaryNeutral => 15
  | .popDirectionalFormat => 16
  | .leftToRightEmbedding => 17
  | .leftToRightOverride => 18
  | .rightToLeftEmbeding => 19
  | .rightToLeftOverride => 20
  | .leftToRightIsolate => 21
  | .rightToLeftIsolate => 22
  | .firstStrongIsolate => 23
  | .popDirectionalIsolate => 24

private def parseNatArray (s : String) : Option (Array Nat) := do
  let mut out := #[]
  for part in s.splitOn " " do
    if part.isEmpty then
      continue
    out := out.push (← part.toNat?)
  return out

private def parseOptNatArray (s : String) : Option (Array (Option Nat)) := do
  let mut out := #[]
  for part in s.splitOn " " do
    if part.isEmpty then
      continue
    if part == "x" then
      out := out.push none
    else
      out := out.push (some (← part.toNat?))
  return out

private def parseQueryOutput (raw : String) : Option BidiResolution := do
  let parts := raw.splitOn ";" |>.toArray
  if parts.size ≠ 3 then
    none
  else
    let paragraphLevel ← parts[0]!.toNat?
    let resolvedLevels ← parseOptNatArray parts[1]!
    let visualOrder ← parseNatArray parts[2]!
    return { paragraphLevel, resolvedLevels, visualOrder }

private def resolveRaw (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) (fileFormat : UInt32) : Except String BidiResolution :=
  let raw := CLib.queryCase text (paragraphDirectionCode paragraphDirection) fileFormat
  if raw.startsWith "ERR:" then
    .error raw
  else
    match parseQueryOutput raw with
    | some out => .ok out
    | none => .error raw

/-- Resolve bidi levels and order for a code-point sequence. -/
public def resolveBidiText (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) : Except String BidiResolution :=
  resolveRaw text paragraphDirection 0

/-- Resolve bidi levels and order for a sequence of bidi classes. -/
public def resolveBidiClasses (classes : Array BidiClass) (paragraphDirection : BidiParagraphDirection) : Except String BidiResolution :=
  resolveRaw (classes.map encodeBidiClass) paragraphDirection 1

end Unicode
