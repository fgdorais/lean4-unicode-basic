/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.BidiClass
public import UnicodeBasic.TableLookup.BidiClass
-- public import UnicodeBasic.TableLookup

/-!
  This file uses lookup tables:
  `BidiClass`.
-/

namespace Unicode

/-- Paragraph direction used for bidi resolution.

  `autoLtr` implements the usual first-strong paragraph direction rule and
  falls back to left-to-right when the paragraph has no strong character.
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

/-- Result of bidi resolution.

  - `paragraphLevel` is the resolved paragraph embedding level.
  - `resolvedLevels` is the per-input-code-point embedding level. `none`
    represents an entry removed by rule X9, such as `BN`, `LRE`, `RLE`, `LRO`,
    `RLO`, or `PDF`.
  - `visualOrder` is the index sequence produced by rule L2 after removing X9
    entries.
-/
public structure BidiResolution where
  paragraphLevel : Nat
  resolvedLevels : Array (Option Nat)
  visualOrder : Array Nat
deriving Inhabited, DecidableEq, Repr

/-- A resolved bidi level attached to an original input code point. -/
public structure BidiLeveledCodepoint where
  index : Nat
  codepoint : UInt32
  level : Nat
deriving Inhabited, DecidableEq, Repr

/-- A contiguous logical run with the same resolved bidi level. -/
public structure BidiRun where
  start : Nat
  stop : Nat
  level : Nat
deriving Inhabited, DecidableEq, Repr

end Unicode

namespace Unicode.BidiInternal

public inductive Override where
  | neutral
  | ltr
  | rtl
deriving Inhabited, DecidableEq

public structure StackEntry where
  level : Nat
  override : Override
  isolate : Bool
  initiator : Option Nat
deriving Inhabited

public structure Item where
  index : Nat
  code : Option UInt32
  orig : BidiClass
  cls : BidiClass
  level : Option Nat
  matchedPDI : Bool
  matchedIsolate : Bool
  matchingInitiator : Option Nat
deriving Inhabited

public abbrev maxExplicitDepth : Nat := 125

public def isIsolateInitiator : BidiClass → Bool
  | .leftToRightIsolate | .rightToLeftIsolate | .firstStrongIsolate => true
  | _ => false

public def isIsolateControl : BidiClass → Bool
  | .leftToRightIsolate | .rightToLeftIsolate | .firstStrongIsolate | .popDirectionalIsolate => true
  | _ => false

public def isRemovedByX9 : BidiClass → Bool
  | .leftToRightEmbedding | .rightToLeftEmbeding | .leftToRightOverride
  | .rightToLeftOverride | .popDirectionalFormat | .boundaryNeutral => true
  | _ => false

public def isNeutral : BidiClass → Bool
  | .otherNeutral | .whiteSpace | .segmentSeparator | .paragraphSeparator
  | .popDirectionalIsolate
  => true
  | _ => false

public def isNeutralItem (item : Item) : Bool :=
  if isIsolateInitiator item.orig then
    item.matchedIsolate
  else
    isNeutral item.cls

public def isNumber : BidiClass → Bool
  | .europeanNumber | .arabicNumber => true
  | _ => false

public def isStrong : BidiClass → Bool
  | .leftToRight | .rightToLeft | .arabicLetter => true
  | _ => false

public def dirClassOfLevel (level : Nat) : BidiClass :=
  if level % 2 == 0 then .leftToRight else .rightToLeft

public def applyOverride (ov : Override) (bc : BidiClass) : BidiClass :=
  match ov with
  | .neutral => bc
  | .ltr => .leftToRight
  | .rtl => .rightToLeft

public def leastGreaterOdd? (level : Nat) : Option Nat :=
  let next := if level % 2 == 0 then level + 1 else level + 2
  if next ≤ maxExplicitDepth then some next else none

public def leastGreaterEven? (level : Nat) : Option Nat :=
  let next := if level % 2 == 0 then level + 2 else level + 1
  if next ≤ maxExplicitDepth then some next else none

public def findMatchingPDI (items : Array Item) (start : Nat) : Option Nat := Id.run do
  let mut depth := 0
  let mut i := start + 1
  while h : i < items.size do
    let bc := items[i].orig
    if isIsolateInitiator bc then
      depth := depth + 1
    else if bc == .popDirectionalIsolate then
      if depth == 0 then
        return some i
      else
        depth := depth - 1
    i := i + 1
  return none

public def firstStrongLevel (items : Array Item) (lo : Nat) (hi : Nat) : Nat := Id.run do
  let mut i := lo
  while i < hi do
    if h : i < items.size then
      match items[i].orig with
      | .leftToRight => return 0
      | .rightToLeft | .arabicLetter => return 1
      | bc =>
          if isIsolateInitiator bc then
            match findMatchingPDI items i with
            | some j => i := j + 1
            | none => return 0
          else
            i := i + 1
    else
      break
  return 0

public def paragraphLevel (items : Array Item) : Unicode.BidiParagraphDirection → Nat
  | .ltr => 0
  | .rtl => 1
  | .autoLtr => firstStrongLevel items 0 items.size

public def buildTextItems (text : Array UInt32) : Array Item := Id.run do
  let mut out := #[]
  for h : i in 0...text.size do
    let c := text[i]
    let bc := lookupBidiClass c
    out := out.push { index := i, code := some c, orig := bc, cls := bc, level := none, matchedPDI := false, matchedIsolate := false, matchingInitiator := none }
  return out

public def buildClassItems (classes : Array BidiClass) : Array Item := Id.run do
  let mut out := #[]
  for h : i in 0...classes.size do
    let bc := classes[i]
    out := out.push { index := i, code := none, orig := bc, cls := bc, level := none, matchedPDI := false, matchedIsolate := false, matchingInitiator := none }
  return out

public abbrev top! (stack : Array StackEntry) : StackEntry :=
  stack.back!

public def pushEmbedding
    (stack : Array StackEntry) (level : Nat) (ov : Override) (overflowIsolate overflowEmbedding : Nat) :
    Array StackEntry × Nat :=
  if overflowIsolate == 0 then
    if overflowEmbedding == 0 then
      (stack.push { level, override := ov, isolate := false, initiator := none }, overflowEmbedding)
    else
      (stack, overflowEmbedding + 1)
  else
    (stack, overflowEmbedding)

end Unicode.BidiInternal
