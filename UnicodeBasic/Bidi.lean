/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup

/-!
  # Bidirectional Resolution

  This module implements the core Unicode Bidirectional Algorithm (UAX #9) in
  Lean and exposes a small public API for resolving embedding levels and visual
  order.
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

private inductive Override where
  | neutral
  | ltr
  | rtl
deriving Inhabited, DecidableEq

private structure StackEntry where
  level : Nat
  override : Override
  isolate : Bool
  initiator : Option Nat
deriving Inhabited

private structure Item where
  index : Nat
  code : Option UInt32
  orig : BidiClass
  cls : BidiClass
  level : Option Nat
  matchedPDI : Bool
  matchedIsolate : Bool
  matchingInitiator : Option Nat
deriving Inhabited

private abbrev maxExplicitDepth : Nat := 125

private def isIsolateInitiator : BidiClass → Bool
  | .leftToRightIsolate | .rightToLeftIsolate | .firstStrongIsolate => true
  | _ => false

private def isIsolateControl : BidiClass → Bool
  | .leftToRightIsolate | .rightToLeftIsolate | .firstStrongIsolate | .popDirectionalIsolate => true
  | _ => false

private def isRemovedByX9 : BidiClass → Bool
  | .leftToRightEmbedding | .rightToLeftEmbeding | .leftToRightOverride
  | .rightToLeftOverride | .popDirectionalFormat | .boundaryNeutral => true
  | _ => false

private def isNeutral : BidiClass → Bool
  | .otherNeutral | .whiteSpace | .segmentSeparator | .paragraphSeparator
  | .popDirectionalIsolate
  => true
  | _ => false

private def isNeutralItem (item : Item) : Bool :=
  if isIsolateInitiator item.orig then
    item.matchedIsolate
  else
    isNeutral item.cls

private def isNumber : BidiClass → Bool
  | .europeanNumber | .arabicNumber => true
  | _ => false

private def isStrong : BidiClass → Bool
  | .leftToRight | .rightToLeft | .arabicLetter => true
  | _ => false

private def dirClassOfLevel (level : Nat) : BidiClass :=
  if level % 2 == 0 then .leftToRight else .rightToLeft

private def applyOverride (ov : Override) (bc : BidiClass) : BidiClass :=
  match ov with
  | .neutral => bc
  | .ltr => .leftToRight
  | .rtl => .rightToLeft

private def leastGreaterOdd? (level : Nat) : Option Nat :=
  let next := if level % 2 == 0 then level + 1 else level + 2
  if next ≤ maxExplicitDepth then some next else none

private def leastGreaterEven? (level : Nat) : Option Nat :=
  let next := if level % 2 == 0 then level + 2 else level + 1
  if next ≤ maxExplicitDepth then some next else none

private def findMatchingPDI (items : Array Item) (start : Nat) : Option Nat := Id.run do
  let mut depth := 0
  let mut i := start + 1
  while i < items.size do
    let bc := items[i]!.orig
    if isIsolateInitiator bc then
      depth := depth + 1
    else if bc == .popDirectionalIsolate then
      if depth == 0 then
        return some i
      else
        depth := depth - 1
    i := i + 1
  return none

private def firstStrongLevel (items : Array Item) (lo : Nat) (hi : Nat) : Nat := Id.run do
  let mut i := lo
  while i < hi && i < items.size do
    match items[i]!.orig with
    | .leftToRight => return 0
    | .rightToLeft | .arabicLetter => return 1
    | bc =>
        if isIsolateInitiator bc then
          match findMatchingPDI items i with
          | some j => i := j + 1
          | none => return 0
        else
          i := i + 1
  return 0

private def paragraphLevel (items : Array Item) : BidiParagraphDirection → Nat
  | .ltr => 0
  | .rtl => 1
  | .autoLtr => firstStrongLevel items 0 items.size

private def buildTextItems (text : Array UInt32) : Array Item := Id.run do
  let mut out := #[]
  for i in [:text.size] do
    let c := text[i]!
    let bc := lookupBidiClass c
    out := out.push { index := i, code := some c, orig := bc, cls := bc, level := none, matchedPDI := false, matchedIsolate := false, matchingInitiator := none }
  return out

private def buildClassItems (classes : Array BidiClass) : Array Item := Id.run do
  let mut out := #[]
  for i in [:classes.size] do
    let bc := classes[i]!
    out := out.push { index := i, code := none, orig := bc, cls := bc, level := none, matchedPDI := false, matchedIsolate := false, matchingInitiator := none }
  return out

private def top! (stack : Array StackEntry) : StackEntry :=
  stack[stack.size - 1]!

private def pushEmbedding
    (stack : Array StackEntry) (level : Nat) (ov : Override) (overflowIsolate overflowEmbedding : Nat) :
    Array StackEntry × Nat :=
  if overflowIsolate == 0 then
    if overflowEmbedding == 0 then
      (stack.push { level, override := ov, isolate := false, initiator := none }, overflowEmbedding)
    else
      (stack, overflowEmbedding + 1)
  else
    (stack, overflowEmbedding)

private def resolveExplicitLevels (paragraph : Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  let mut stack : Array StackEntry := #[{ level := paragraph, override := .neutral, isolate := false, initiator := none }]
  let mut overflowIsolate := 0
  let mut overflowEmbedding := 0
  let mut validIsolate := 0
  for i in [:items.size] do
    let item := items[i]!
    let cur := top! stack
    match item.orig with
    | .leftToRightEmbedding =>
        match leastGreaterEven? cur.level with
        | some level =>
            let r := pushEmbedding stack level .neutral overflowIsolate overflowEmbedding
            stack := r.1
            overflowEmbedding := r.2
        | none =>
            if overflowIsolate == 0 then overflowEmbedding := overflowEmbedding + 1
    | .rightToLeftEmbeding =>
        match leastGreaterOdd? cur.level with
        | some level =>
            let r := pushEmbedding stack level .neutral overflowIsolate overflowEmbedding
            stack := r.1
            overflowEmbedding := r.2
        | none =>
            if overflowIsolate == 0 then overflowEmbedding := overflowEmbedding + 1
    | .leftToRightOverride =>
        match leastGreaterEven? cur.level with
        | some level =>
            let r := pushEmbedding stack level .ltr overflowIsolate overflowEmbedding
            stack := r.1
            overflowEmbedding := r.2
        | none =>
            if overflowIsolate == 0 then overflowEmbedding := overflowEmbedding + 1
    | .rightToLeftOverride =>
        match leastGreaterOdd? cur.level with
        | some level =>
            let r := pushEmbedding stack level .rtl overflowIsolate overflowEmbedding
            stack := r.1
            overflowEmbedding := r.2
        | none =>
            if overflowIsolate == 0 then overflowEmbedding := overflowEmbedding + 1
    | .leftToRightIsolate | .rightToLeftIsolate | .firstStrongIsolate =>
        let initiatorClass :=
          if item.orig == .firstStrongIsolate then
            if firstStrongLevel items (i + 1) (match findMatchingPDI items i with | some j => j | none => items.size) == 0 then
              BidiClass.leftToRightIsolate
            else
              BidiClass.rightToLeftIsolate
          else
            item.orig
        items := items.set! i { item with cls := applyOverride cur.override initiatorClass, level := some cur.level }
        let next? :=
          if initiatorClass == .rightToLeftIsolate then leastGreaterOdd? cur.level else leastGreaterEven? cur.level
        match next? with
        | some level =>
            if overflowIsolate == 0 && overflowEmbedding == 0 then
              stack := stack.push { level, override := .neutral, isolate := true, initiator := some i }
              validIsolate := validIsolate + 1
            else
              overflowIsolate := overflowIsolate + 1
        | none =>
            overflowIsolate := overflowIsolate + 1
    | .popDirectionalIsolate =>
        let mut matchedPDI := false
        let mut matchingInitiator : Option Nat := none
        if overflowIsolate > 0 then
          overflowIsolate := overflowIsolate - 1
        else if validIsolate > 0 then
          matchedPDI := true
          overflowEmbedding := 0
          while stack.size > 1 && !(top! stack).isolate do
            stack := stack.pop
          matchingInitiator := (top! stack).initiator
          match matchingInitiator with
          | some start =>
              items := items.set! start { items[start]! with matchedIsolate := true }
          | none => pure ()
          if stack.size > 1 then
            stack := stack.pop
          validIsolate := validIsolate - 1
        let cur := top! stack
        items := items.set! i { item with cls := applyOverride cur.override item.orig, level := some cur.level, matchedPDI, matchingInitiator }
    | .popDirectionalFormat =>
        if overflowIsolate > 0 then
          pure ()
        else if overflowEmbedding > 0 then
          overflowEmbedding := overflowEmbedding - 1
        else if !(top! stack).isolate && stack.size > 1 then
          stack := stack.pop
    | .paragraphSeparator =>
        items := items.set! i { item with level := some paragraph }
    | _ =>
        if !isRemovedByX9 item.orig then
          items := items.set! i { item with cls := applyOverride cur.override item.orig, level := some cur.level }
  for i in [:items.size] do
    let item := items[i]!
    if isRemovedByX9 item.orig then
      items := items.set! i { item with level := none }
  return items

private def previousInSeq? (items : Array Item) (seq : Array Nat) (pos : Nat) : Option BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    let bc := items[seq[j]!]!.cls
    if !isRemovedByX9 bc then
      return some bc
  return none

private def nextInSeq? (items : Array Item) (seq : Array Nat) (pos : Nat) : Option BidiClass := Id.run do
  let mut j := pos + 1
  while j < seq.size do
    let bc := items[seq[j]!]!.cls
    if !isRemovedByX9 bc then
      return some bc
    j := j + 1
  return none

private def setClass (items : Array Item) (i : Nat) (bc : BidiClass) : Array Item :=
  items.set! i { items[i]! with cls := bc }

private def prevStrongOrSot (items : Array Item) (seq : Array Nat) (pos : Nat) (sot : BidiClass) : BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    let bc := items[seq[j]!]!.cls
    if isStrong bc then
      return bc
  return sot

private def resolveWeak (sot : BidiClass) (seq : Array Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .nonspacingMark then
      items := setClass items i (match previousInSeq? items seq pos with | some bc => bc | none => sot)
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .europeanNumber then
      let prev := prevStrongOrSot items seq pos sot
      if prev == .arabicLetter then
        items := setClass items i .arabicNumber
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .arabicLetter then
      items := setClass items i .rightToLeft
  if seq.size ≥ 3 then
    for pos in [1:seq.size - 1] do
      let i := seq[pos]!
      let bc := items[i]!.cls
      let prev := items[seq[pos - 1]!]!.cls
      let next := items[seq[pos + 1]!]!.cls
      if bc == .europeanSeparator && prev == .europeanNumber && next == .europeanNumber then
        items := setClass items i .europeanNumber
      else if bc == .commonSeparator && prev == .europeanNumber && next == .europeanNumber then
        items := setClass items i .europeanNumber
      else if bc == .commonSeparator && prev == .arabicNumber && next == .arabicNumber then
        items := setClass items i .arabicNumber
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .europeanTerminator then
      let mut hasEN := false
      let mut j := pos
      while j > 0 && items[seq[j - 1]!]!.cls == .europeanTerminator do
        j := j - 1
      if j > 0 && items[seq[j - 1]!]!.cls == .europeanNumber then
        hasEN := true
      j := pos + 1
      while j < seq.size && items[seq[j]!]!.cls == .europeanTerminator do
        j := j + 1
      if j < seq.size && items[seq[j]!]!.cls == .europeanNumber then
        hasEN := true
      if hasEN then
        items := setClass items i .europeanNumber
  for pos in [:seq.size] do
    let i := seq[pos]!
    match items[i]!.cls with
    | .europeanSeparator | .commonSeparator | .europeanTerminator =>
        items := setClass items i .otherNeutral
    | _ => pure ()
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .europeanNumber then
      let prev := prevStrongOrSot items seq pos sot
      if prev == .leftToRight then
        items := setClass items i .leftToRight
  return items

private structure BracketOpen where
  pos : Nat
  pair : UInt32
deriving Inhabited

private def canonicalBracketKey (c : UInt32) : UInt32 :=
  if c == 0x2329 then 0x3008
  else if c == 0x232A then 0x3009
  else c

private def strongOrNumberForBracket : BidiClass → Option BidiClass
  | .leftToRight => some .leftToRight
  | .rightToLeft | .arabicNumber | .europeanNumber => some .rightToLeft
  | _ => none

private def prevBracketContextOrSot (items : Array Item) (seq : Array Nat) (pos : Nat) (sot : BidiClass) : BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    match strongOrNumberForBracket items[seq[j]!]!.cls with
    | some bc => return bc
    | none => pure ()
  return sot

private def resolveBrackets (sot : BidiClass) (seq : Array Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  let mut pairs : Array (Nat × Nat) := #[]
  let mut stack : Array BracketOpen := #[]
  let mut overflowBrackets := 0
  let mut overflowSeen := false
  for pos in [:seq.size] do
    let i := seq[pos]!
    if items[i]!.cls == .otherNeutral then
      match items[i]!.code with
      | none => pure ()
      | some c =>
          match lookupBidiPairedBracketType? c with
          | some .openBracket =>
              if stack.size < 63 then
                match lookupBidiPairedBracket? c with
                | some p => stack := stack.push { pos, pair := canonicalBracketKey p }
                | none => pure ()
              else
                overflowBrackets := overflowBrackets + 1
                overflowSeen := true
          | some .closeBracket =>
              if overflowBrackets > 0 then
                overflowBrackets := overflowBrackets - 1
              else
                let mut found : Option Nat := none
                let mut j := stack.size
                while j > 0 && found.isNone do
                  j := j - 1
                  if stack[j]!.pair == canonicalBracketKey c then
                    found := some j
                match found with
                | none => pure ()
                | some foundAt =>
                    pairs := pairs.push (stack[foundAt]!.pos, pos)
                    stack := stack.extract 0 foundAt
          | none => pure ()
  let processPairs := if overflowSeen then #[] else pairs
  for p in processPairs.qsort (fun a b => if a.1 == b.1 then a.2 < b.2 else a.1 < b.1) do
    let openPos := p.1
    let closePos := p.2
    let embedding := dirClassOfLevel (items[seq[openPos]!]!.level.getD 0)
    let opposite := if embedding == .leftToRight then BidiClass.rightToLeft else BidiClass.leftToRight
    let mut hasEmbedding := false
    let mut hasOpposite := false
    let mut k := openPos + 1
    while k < closePos do
      match strongOrNumberForBracket items[seq[k]!]!.cls with
      | some bc =>
          if bc == embedding then
            hasEmbedding := true
          else if bc == opposite then
            hasOpposite := true
      | none => pure ()
      k := k + 1
    if hasEmbedding || hasOpposite then
      let resolved :=
        if hasEmbedding then
          embedding
        else
          let before := prevBracketContextOrSot items seq openPos sot
          if before == opposite then opposite else embedding
      items := setClass items seq[openPos]! resolved
      items := setClass items seq[closePos]! resolved
      let mut openNsm := openPos + 1
      while openNsm < seq.size && items[seq[openNsm]!]!.orig == .nonspacingMark do
        items := setClass items seq[openNsm]! resolved
        openNsm := openNsm + 1
      let mut closeNsm := closePos + 1
      while closeNsm < seq.size && items[seq[closeNsm]!]!.orig == .nonspacingMark do
        items := setClass items seq[closeNsm]! resolved
        closeNsm := closeNsm + 1
      let mut j := openPos + 1
      while j < closePos do
        let ix := seq[j]!
        if items[ix]!.cls == .nonspacingMark then
          items := setClass items ix resolved
        j := j + 1
  return items

private def resolveNeutrals (sot eot : BidiClass) (seq : Array Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  let mut pos := 0
  while pos < seq.size do
    let i := seq[pos]!
    if !isNeutralItem items[i]! then
      pos := pos + 1
    else
      let start := pos
      while pos < seq.size && isNeutralItem items[seq[pos]!]! do
        pos := pos + 1
      let stop := pos
      let before := if start == 0 then sot else items[seq[start - 1]!]!.cls
      let after := if stop == seq.size then eot else items[seq[stop]!]!.cls
      let beforeDir := if before == .leftToRight then .leftToRight else if before == .rightToLeft || isNumber before then .rightToLeft else sot
      let afterDir := if after == .leftToRight then .leftToRight else if after == .rightToLeft || isNumber after then .rightToLeft else eot
      let resolved := if beforeDir == afterDir then beforeDir else dirClassOfLevel (items[i]!.level.getD 0)
      for j in [start:stop] do
        items := setClass items seq[j]! resolved
  return items

private def contiguousLevelRuns (items : Array Item) : Array (Array Nat) := Id.run do
  let mut runs := #[]
  let mut i := 0
  while i < items.size do
    match items[i]!.level with
    | none => i := i + 1
    | some level =>
        let mut run := #[]
        while i < items.size && (items[i]!.level.isNone || items[i]!.level == some level) do
          if items[i]!.level == some level then
            run := run.push i
          i := i + 1
        runs := runs.push run
  return runs

private def previousRunLevel (runs : Array (Array Nat)) (r : Nat) (items : Array Item) (paragraph : Nat) : Nat :=
  let first := items[runs[r]![0]!]!
  match first.matchingInitiator with
  | some i => items[i]!.level.getD paragraph
  | none => if r == 0 then paragraph else items[runs[r - 1]![0]!]!.level.getD paragraph

private def nextRunLevel (runs : Array (Array Nat)) (r : Nat) (items : Array Item) (paragraph : Nat) : Nat := Id.run do
  let last := items[runs[r]![runs[r]!.size - 1]!]!
  if isIsolateInitiator last.orig then
    let mut found : Option Nat := none
    for item in items do
      if item.matchingInitiator == some last.index then
        found := item.level
    return found.getD paragraph
  else
    return if r + 1 < runs.size then items[runs[r + 1]![0]!]!.level.getD paragraph else paragraph

private def findMatchingPdiIndex (items : Array Item) (initiator : Nat) : Option Nat := Id.run do
  for item in items do
    if item.matchingInitiator == some initiator then
      return some item.index
  return none

private def findRunStartingAt (runs : Array (Array Nat)) (i : Nat) : Option Nat := Id.run do
  for r in [:runs.size] do
    if runs[r]!.size > 0 && runs[r]![0]! == i then
      return some r
  return none

private def resolveRuns (paragraph : Nat) (items0 : Array Item) : Array Item := Id.run do
  let runs := contiguousLevelRuns items0
  let mut items := items0
  let mut visited : Array Bool := Array.replicate runs.size false
  for r in [:runs.size] do
    if visited[r]! then
      continue
    let seq := runs[r]!
    if seq.size == 0 then
      continue
    let mut seq := seq
    let mut lastRun := r
    visited := visited.set! r true
    let mut keepGoing := true
    while keepGoing do
      keepGoing := false
      let lastIndex := runs[lastRun]![runs[lastRun]!.size - 1]!
      let lastItem := items[lastIndex]!
      if isIsolateInitiator lastItem.orig && lastItem.matchedIsolate then
        match findMatchingPdiIndex items lastItem.index with
        | some pdi =>
            match findRunStartingAt runs pdi with
            | some nextRun =>
                if nextRun != lastRun && !visited[nextRun]! then
                  seq := seq ++ runs[nextRun]!
                  visited := visited.set! nextRun true
                  lastRun := nextRun
                  keepGoing := true
            | none => pure ()
        | none => pure ()
    let level := items[seq[0]!]!.level.getD paragraph
    let sot := dirClassOfLevel (max level (previousRunLevel runs r items paragraph))
    let eot := dirClassOfLevel (max (items[seq[seq.size - 1]!]!.level.getD paragraph) (nextRunLevel runs lastRun items paragraph))
    items := resolveWeak sot seq items
    items := resolveBrackets sot seq items
    items := resolveNeutrals sot eot seq items
  return items

private def resolveImplicitLevels (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  for i in [:items.size] do
    match items[i]!.level with
    | none => pure ()
    | some level =>
        if isIsolateInitiator items[i]!.orig && !items[i]!.matchedIsolate then
          pure ()
        else
          let bc := items[i]!.cls
          let level :=
            if level % 2 == 0 then
              if bc == .rightToLeft then level + 1
              else if bc == .arabicNumber || bc == .europeanNumber then level + 2
              else level
            else
              if bc == .leftToRight || bc == .arabicNumber || bc == .europeanNumber then level + 1
              else level
          items := items.set! i { items[i]! with level := some level }
  return items

private def resetWhitespaceBefore (paragraph : Nat) (items0 : Array Item) (stop : Nat) : Array Item := Id.run do
  let mut items := items0
  let mut j := stop
  while j > 0 do
    let k := j - 1
    let bc := items[k]!.orig
    if bc == .whiteSpace || isIsolateControl bc || items[k]!.level.isNone then
      items := items.set! k { items[k]! with level := if items[k]!.level.isSome then some paragraph else none }
      j := k
    else
      return items
  return items

private def resolveLineBreaks (paragraph : Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  for i in [:items.size] do
    let bc := items[i]!.orig
    if bc == .segmentSeparator || bc == .paragraphSeparator then
      items := resetWhitespaceBefore paragraph items i
      if items[i]!.level.isSome then
        items := items.set! i { items[i]! with level := some paragraph }
  items := resetWhitespaceBefore paragraph items items.size
  return items

private def reverseSegment (order : Array Nat) (lo hi : Nat) : Array Nat := Id.run do
  let mut out := order
  let mut l := lo
  let mut r := hi
  while l < r do
    r := r - 1
    let a := out[l]!
    let b := out[r]!
    out := out.set! l b
    out := out.set! r a
    l := l + 1
  return out

private def visualOrder (items : Array Item) : Array Nat := Id.run do
  let mut order := #[]
  let mut maxLevel := 0
  let mut minOdd : Option Nat := none
  for item in items do
    match item.level with
    | none => pure ()
    | some level =>
        order := order.push item.index
        if level > maxLevel then
          maxLevel := level
        if level % 2 == 1 then
          minOdd := some (match minOdd with | none => level | some m => min m level)
  match minOdd with
  | none => order
  | some low =>
      let mut lev := maxLevel + 1
      while lev > low do
        lev := lev - 1
        let mut i := 0
        while i < order.size do
          match items[order[i]!]!.level with
          | some l =>
              if l ≥ lev then
                let start := i
                while i < order.size && (items[order[i]!]!.level.getD 0) ≥ lev do
                  i := i + 1
                order := reverseSegment order start i
              else
                i := i + 1
          | none => i := i + 1
      order

private def resolveItems (items0 : Array Item) (direction : BidiParagraphDirection) : BidiResolution :=
  let paragraph := paragraphLevel items0 direction
  let items := resolveExplicitLevels paragraph items0
  let items := resolveRuns paragraph items
  let items := resolveImplicitLevels items
  let items := resolveLineBreaks paragraph items
  {
    paragraphLevel := paragraph
    resolvedLevels := items.map (·.level)
    visualOrder := visualOrder items
  }

/-- Resolve bidi levels and visual order for a code-point sequence.

  Code points are first mapped through the generated `Bidi_Class` table, then
  the Unicode Bidirectional Algorithm is applied. Paired-bracket processing uses
  `BidiBrackets.txt` data when code points are available.
-/
public def resolveBidiText
    (text : Array UInt32) (paragraphDirection : BidiParagraphDirection) :
    BidiResolution :=
  resolveItems (buildTextItems text) paragraphDirection

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
  for i in [:text.size] do
    if i < resolution.resolvedLevels.size then
      match resolution.resolvedLevels[i]! with
      | some level => out := out.push { index := i, codepoint := text[i]!, level }
      | none => pure ()
  return out

/-- Return the input code points in resolved visual order.

  X9-removed entries are omitted because `BidiResolution.visualOrder` contains
  only indexes with concrete resolved levels.
-/
public def reorderBidiText (text : Array UInt32) (resolution : BidiResolution) : Array UInt32 := Id.run do
  let mut out := #[]
  for i in resolution.visualOrder do
    if i < text.size then
      out := out.push text[i]!
  return out

/-- Return contiguous logical runs with the same resolved bidi level.

  Runs are half-open code-point index ranges `[start, stop)`. X9-removed entries
  are skipped and therefore break runs.
-/
public def bidiRuns (resolution : BidiResolution) : Array BidiRun := Id.run do
  let levels := resolution.resolvedLevels
  let mut runs := #[]
  let mut i := 0
  while i < levels.size do
    match levels[i]! with
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
  resolveItems (buildClassItems classes) paragraphDirection

end Unicode
