/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Types

/-!
  # Bidirectional Resolution

  This module exposes the public Lean-facing bidi API.

  The vendored Unicode bidi reference implementation remains hidden behind the
  Lean wrappers here. The raw `br_*` symbols are implementation details and are
  not part of the public API surface.
-/

namespace Unicode

/-- Error values returned by bidi bridge operations. -/
public inductive BidiError where
  | initFailed (code : Int)
  | allocationFailed
  | queryFailed (code : Int)
  | invalidOutput (output : String)
deriving Inhabited, DecidableEq, Repr

public instance : ToString BidiError where
  toString
  | .initFailed code => s!"initFailed({code})"
  | .allocationFailed => "allocationFailed"
  | .queryFailed code => s!"queryFailed({code})"
  | .invalidOutput output => s!"invalidOutput({output})"

/-- Handle for an initialized bidi bridge.

  The `dataDir` field records the Unicode data directory used to initialize the
  reference implementation.
-/
public structure BidiContext where
  dataDir : String
deriving Inhabited, DecidableEq, Repr

/-- Paragraph direction used for bidi resolution.

  This maps to the paragraph-direction codes accepted by the vendored Unicode
  bidi reference implementation.
-/
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

/-- Result of a bidi resolution query.

  - `paragraphLevel` is the resolved paragraph embedding level.
  - `resolvedLevels` is the per-code-point embedding level output, where `none`
    represents an ignorable entry in the reference output.
  - `visualOrder` is the visual reordering index sequence.
-/
public structure BidiResolution where
  paragraphLevel : Nat
  resolvedLevels : Array (Option Nat)
  visualOrder : Array Nat
deriving Inhabited, DecidableEq, Repr

namespace CLib

/-- Initialize the bidi reference implementation for a given Unicode data directory.

  The returned context is an opaque handle that should be threaded through
  subsequent bidi queries.
-/
@[extern "unicode_bidi_init"]
protected opaque mkContext (dataDir : String) : Except BidiError BidiContext

/-- Query the bidi reference implementation for a code-point sequence.

  This is a low-level bridge used by the public Lean wrappers in this module.
-/
@[extern "unicode_bidi_query_case"]
protected opaque queryCase
    (ctx : BidiContext) (text : Array UInt32) (paragraphDirection : UInt32) (fileFormat : UInt32) :
    Except BidiError String

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

private def parseQueryOutput (raw : String) : Except BidiError BidiResolution := do
  let parts := raw.splitOn ";" |>.toArray
  if parts.size ≠ 3 then
    throw (.invalidOutput raw)
  let paragraphLevel ←
    match parts[0]!.toNat? with
    | some n => pure n
    | none => throw (.invalidOutput raw)
  let resolvedLevels ←
    match parseOptNatArray parts[1]! with
    | some xs => pure xs
    | none => throw (.invalidOutput raw)
  let visualOrder ←
    match parseNatArray parts[2]! with
    | some xs => pure xs
    | none => throw (.invalidOutput raw)
  pure { paragraphLevel, resolvedLevels, visualOrder }

private def resolveRaw
    (ctx : BidiContext) (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) (fileFormat : UInt32) :
    Except BidiError BidiResolution := do
  let raw ← CLib.queryCase ctx text (paragraphDirectionCode paragraphDirection) fileFormat
  parseQueryOutput raw

/-- Initialize the bidi reference implementation.

  The returned handle should be passed to `resolveBidiText` or
  `resolveBidiClasses`.
-/
public def bidiInit (dataDir : String) : Except BidiError BidiContext :=
  CLib.mkContext dataDir

/-- Resolve bidi levels and order for a code-point sequence.

  This is the public Lean wrapper around the vendored Unicode bidi reference
  implementation.

  The `ctx` argument is the opaque handle returned by `bidiInit`.

  Returns `Except.error` when the bridge reports an initialization or query
  failure, or when its output cannot be parsed.
-/
public def resolveBidiText
    (ctx : BidiContext) (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) :
    Except BidiError BidiResolution :=
  resolveRaw ctx text paragraphDirection 0

/-- Resolve bidi levels and order for a sequence of bidi classes.

  This is the same public wrapper as `resolveBidiText`, but it accepts bidi
  classes directly instead of code points. It is primarily useful for tests or
  debugging rule behavior independently from property lookup.

  The `ctx` argument is the opaque handle returned by `bidiInit`.
-/
public def resolveBidiClasses
    (ctx : BidiContext) (classes : Array BidiClass) (paragraphDirection : BidiParagraphDirection) :
    Except BidiError BidiResolution :=
  resolveRaw ctx (classes.map encodeBidiClass) paragraphDirection 1

end Unicode
