/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi.Output

namespace Unicode

/-- Resolve bidi levels and visual order for a code-point sequence.

  Code points are first mapped through the generated `Bidi_Class` table, then
  the Unicode Bidirectional Algorithm is applied. Paired-bracket processing uses
  `BidiBrackets.txt` data when code points are available.
-/
public def resolveBidiText
    (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) :
    BidiResolution :=
  BidiInternal.resolveItems (BidiInternal.buildTextItems text) paragraphDirection

/-- Convert a Lean string to Unicode scalar values.

  This helper exposes the input shape expected by `resolveBidiText`.
-/
public def bidiCodepointsOfString (s : String) : Array UInt32 :=
  s.toList.toArray.map (·.val)

/-- Resolve bidi levels and visual order for a Lean string.

  The result uses code-point indexes into `bidiCodepointsOfString s`.
-/
public def resolveBidiString
    (s : String) (paragraphDirection : BidiParagraphDirection) :
    BidiResolution :=
  resolveBidiText (bidiCodepointsOfString s) paragraphDirection

/-- Pair each non-X9 input code point with its resolved level.

  Entries whose level is `none` in `BidiResolution.resolvedLevels` are omitted.
-/
public def bidiLeveledCodepoints
    (text : Array UInt32) (resolution : BidiResolution) :
    Array BidiLeveledCodepoint := Id.run do
  let mut out := #[]
  for h : i in 0...text.size do
    if hi : i < resolution.resolvedLevels.size then
      match resolution.resolvedLevels[i]'hi with
      | some level => out := out.push { index := i, codepoint := text[i], level }
      | none => pure ()
  return out

/-- Return the input code points in resolved visual order.

  X9-removed entries are omitted because `BidiResolution.visualOrder` contains
  only indexes with concrete resolved levels.
-/
public def reorderBidiText (text : Array UInt32) (resolution : BidiResolution) : Array UInt32 := Id.run do
  let mut out := #[]
  for i in resolution.visualOrder do
    if hi : i < text.size then
      out := out.push text[i]
  return out

/-- Return contiguous logical runs with the same resolved bidi level.

  Runs are half-open code-point index ranges `[start, stop)`. X9-removed entries
  are skipped and therefore break runs.
-/
public def bidiRuns (resolution : BidiResolution) : Array BidiRun := Id.run do
  let levels := resolution.resolvedLevels
  let mut runs := #[]
  let mut i := 0
  while h : i < levels.size do
    match levels[i] with
    | none => i := i + 1
    | some level =>
        let start := i
        i := i + 1
        while i < levels.size && levels[i]! == some level do
          i := i + 1
        runs := runs.push { start, stop := i, level }
  return runs

/-- Resolve bidi levels and visual order for a sequence of bidi classes.

  This is useful for conformance tests and for debugging the algorithm without
  involving property lookup. Because no code points are available, paired-bracket
  processing cannot identify bracket pairs and therefore treats `ON` values as
  ordinary neutrals.
-/
public def resolveBidiClasses
    (classes : Array BidiClass) (paragraphDirection : BidiParagraphDirection) :
    BidiResolution :=
  BidiInternal.resolveItems (BidiInternal.buildClassItems classes) paragraphDirection

end Unicode
