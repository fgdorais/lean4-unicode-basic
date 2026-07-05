/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi.Explicit
public import UnicodeBasic.TableLookup.BidiBrackets

/-!
  This file uses lookup tables:
  `BidiBrackets`.
-/

namespace Unicode.BidiInternal

public def resolveWeak {n : Nat} (sot : BidiClass) (seq : Array (Fin n)) (items0 : Vector Item n) : Vector Item n := Id.run do
  let mut items := items0
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .nonspacingMark then
      items := setClass items i (match previousInSeq? items seq pos with | some bc => bc | none => sot)
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .europeanNumber then
      let prev := prevStrongOrSot items seq pos sot
      if prev == .arabicLetter then
        items := setClass items i .arabicNumber
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .arabicLetter then
      items := setClass items i .rightToLeft
  if seq.size ≥ 3 then
    for h : pos in 1...seq.size - 1 do
      let i := seq[pos]
      let bc := (items.get i).cls
      have hprev : pos - 1 < seq.size := by get_elem_tactic
      have hnext : pos + 1 < seq.size := by get_elem_tactic
      let prev := (items.get (seq[pos - 1]'hprev)).cls
      let next := (items.get (seq[pos + 1]'hnext)).cls
      if bc == .europeanSeparator && prev == .europeanNumber && next == .europeanNumber then
        items := setClass items i .europeanNumber
      else if bc == .commonSeparator && prev == .europeanNumber && next == .europeanNumber then
        items := setClass items i .europeanNumber
      else if bc == .commonSeparator && prev == .arabicNumber && next == .arabicNumber then
        items := setClass items i .arabicNumber
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .europeanTerminator then
      let mut hasEN := false
      let mut j := pos
      while j > 0 && (if hj : j - 1 < seq.size then (items.get (seq[j - 1]'hj)).cls == .europeanTerminator else false) do
        j := j - 1
      if j > 0 then
        if hj : j - 1 < seq.size then
          if (items.get (seq[j - 1]'hj)).cls == .europeanNumber then hasEN := true
      j := pos + 1
      while j < seq.size && (if hj : j < seq.size then (items.get (seq[j]'hj)).cls == .europeanTerminator else false) do
        j := j + 1
      if j < seq.size then
        if hj : j < seq.size then
          if (items.get (seq[j]'hj)).cls == .europeanNumber then hasEN := true
      if hasEN then
        items := setClass items i .europeanNumber
  for h : pos in 0...seq.size do
    let i := seq[pos]
    match (items.get i).cls with
    | .europeanSeparator | .commonSeparator | .europeanTerminator =>
        items := setClass items i .otherNeutral
    | _ => pure ()
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .europeanNumber then
      let prev := prevStrongOrSot items seq pos sot
      if prev == .leftToRight then
        items := setClass items i .leftToRight
  return items

public structure BracketOpen where
  pos : Nat
  pair : UInt32
deriving Inhabited

public def canonicalBracketKey (c : UInt32) : UInt32 :=
  if c == 0x2329 then 0x3008
  else if c == 0x232A then 0x3009
  else c

public def strongOrNumberForBracket : BidiClass → Option BidiClass
  | .leftToRight => some .leftToRight
  | .rightToLeft | .arabicNumber | .europeanNumber => some .rightToLeft
  | _ => none

public def prevBracketContextOrSot {n : Nat} (items : Vector Item n) (seq : Array (Fin n)) (pos : Nat) (sot : BidiClass) : BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    if h : j < seq.size then
      match strongOrNumberForBracket (items.get seq[j]).cls with
      | some bc => return bc
      | none => pure ()
  return sot

public def resolveBrackets {n : Nat} (sot : BidiClass) (seq : Array (Fin n)) (items0 : Vector Item n) : Vector Item n := Id.run do
  let mut items := items0
  let mut pairs : Array (Nat × Nat) := #[]
  let mut stack : Array BracketOpen := #[]
  let mut overflowBrackets := 0
  let mut overflowSeen := false
  for h : pos in 0...seq.size do
    let i := seq[pos]
    if (items.get i).cls == .otherNeutral then
      match (items.get i).code with
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
                  if hj : j < stack.size then
                    if stack[j].pair == canonicalBracketKey c then
                      found := some j
                match found with
                | none => pure ()
                | some foundAt =>
                    if hf : foundAt < stack.size then
                      pairs := pairs.push (stack[foundAt].pos, pos)
                    stack := stack.extract 0 foundAt
          | none => pure ()
  let processPairs := if overflowSeen then #[] else pairs
  for p in processPairs.qsort (fun a b => if a.1 == b.1 then a.2 < b.2 else a.1 < b.1) do
    let openPos := p.1
    let closePos := p.2
    if ho : openPos < seq.size then
      let embedding := dirClassOfLevel ((items.get (seq[openPos]'ho)).level.getD 0)
      let opposite := if embedding == .leftToRight then BidiClass.rightToLeft else BidiClass.leftToRight
      let mut hasEmbedding := false
      let mut hasOpposite := false
      let mut k := openPos + 1
      while k < closePos do
        if hk : k < seq.size then
          match strongOrNumberForBracket (items.get seq[k]).cls with
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
        if hc : closePos < seq.size then
          items := setClass items (seq[openPos]'ho) resolved
          items := setClass items (seq[closePos]'hc) resolved
          let mut openNsm := openPos + 1
          while openNsm < seq.size && (if hm : openNsm < seq.size then (items.get (seq[openNsm]'hm)).orig == .nonspacingMark else false) do
            if hm : openNsm < seq.size then
              items := setClass items (seq[openNsm]'hm) resolved
            openNsm := openNsm + 1
          let mut closeNsm := closePos + 1
          while closeNsm < seq.size && (if hm : closeNsm < seq.size then (items.get (seq[closeNsm]'hm)).orig == .nonspacingMark else false) do
            if hm : closeNsm < seq.size then
              items := setClass items (seq[closeNsm]'hm) resolved
            closeNsm := closeNsm + 1
          let mut j := openPos + 1
          while j < closePos do
            if hj : j < seq.size then
              if (items.get (seq[j]'hj)).cls == .nonspacingMark then
                items := setClass items (seq[j]'hj) resolved
            j := j + 1
  return items

public def resolveNeutrals {n : Nat} (sot eot : BidiClass) (seq : Array (Fin n)) (items0 : Vector Item n) : Vector Item n := Id.run do
  let mut items := items0
  let mut pos := 0
  while pos < seq.size do
    if hp : pos < seq.size then
      let i := (seq[pos]'hp)
      if !isNeutralItem (items.get i) then
        pos := pos + 1
      else
        let start := pos
        while pos < seq.size && (if hp2 : pos < seq.size then isNeutralItem (items.get (seq[pos]'hp2)) else false) do
          pos := pos + 1
        let stop := pos
        let before := if start == 0 then sot else
          if hs : start - 1 < seq.size then (items.get (seq[start - 1]'hs)).cls else sot
        let after := if stop == seq.size then eot else
          if hs : stop < seq.size then (items.get (seq[stop]'hs)).cls else eot
        let beforeDir := if before == .leftToRight then .leftToRight else if before == .rightToLeft || isNumber before then .rightToLeft else sot
        let afterDir := if after == .leftToRight then .leftToRight else if after == .rightToLeft || isNumber after then .rightToLeft else eot
        let resolved := if beforeDir == afterDir then beforeDir else dirClassOfLevel ((items.get i).level.getD 0)
        for h : j in start...stop do
          if hj : j < seq.size then
            items := setClass items seq[j] resolved
    else
      break
  return items

public def contiguousLevelRuns {n : Nat} (items : Vector Item n) : Array (Array (Fin n)) := Id.run do
  let mut runs : Array (Array (Fin n)) := #[]
  let mut i := 0
  while h : i < n do
    match (items.get ⟨i, h⟩).level with
    | none => i := i + 1
    | some level =>
        let mut run : Array (Fin n) := #[]
        let mut cont := true
        while cont do
          if h2 : i < n then
            let entry := items.get ⟨i, h2⟩
            if entry.level.isNone || entry.level == some level then
              if entry.level == some level then
                run := run.push ⟨i, h2⟩
              i := i + 1
            else
              cont := false
          else
            cont := false
        if run.size > 0 then
          runs := runs.push run
  return runs

public def previousRunLevel {n : Nat} (runs : Array (Array (Fin n))) (r : Nat) (items : Vector Item n) (paragraph : Nat) : Nat :=
  if hr : r < runs.size then
    let run := runs[r]
    if h0 : 0 < run.size then
      let first := items.get (run[0]'h0)
      match first.matchingInitiator with
      | some i =>
          if hi : i < n then (items.get ⟨i, hi⟩).level.getD paragraph else paragraph
      | none =>
          if r == 0 then paragraph else
            if hr1 : r - 1 < runs.size then
              let prevRun := runs[r - 1]
              if h01 : 0 < prevRun.size then
                (items.get (prevRun[0]'h01)).level.getD paragraph
              else paragraph
            else paragraph
    else paragraph
  else paragraph

public def nextRunLevel {n : Nat} (runs : Array (Array (Fin n))) (r : Nat) (items : Vector Item n) (paragraph : Nat) : Nat := Id.run do
  if hr : r < runs.size then
    let run := runs[r]
    if h0 : 0 < run.size then
      have hlast : run.size - 1 < run.size := by omega
      let last := items.get (run[run.size - 1]'hlast)
      if isIsolateInitiator last.orig then
        let mut found : Option Nat := none
        for item in items.toArray do
          if item.matchingInitiator == some last.index then
            found := item.level
        return found.getD paragraph
      else
        if hr1 : r + 1 < runs.size then
          let nextRun := runs[r + 1]
          if h01 : 0 < nextRun.size then
            return (items.get (nextRun[0]'h01)).level.getD paragraph
          else return paragraph
        else return paragraph
    else return paragraph
  else return paragraph

public def findMatchingPdiIndex {n : Nat} (items : Vector Item n) (initiator : Nat) : Option Nat := Id.run do
  for item in items.toArray do
    if item.matchingInitiator == some initiator then
      return some item.index
  return none

-- Returns the run index (as Fin runs.size) whose first element has value i.
public def findRunStartingAt {n : Nat} (runs : Array (Array (Fin n))) (i : Nat) : Option {r : Fin runs.size // 0 < (runs[r]).size} := Id.run do
  let mut r := 0
  while h : r < runs.size do
    let run := runs[r]
    if h0 : 0 < run.size then
      if (run[0]'h0).val == i then
        return some ⟨⟨r, h⟩, h0⟩
    r := r + 1
  return none

public def resolveRuns {n : Nat} (paragraph : Nat) (items0 : Vector Item n) : Vector Item n := Id.run do
  let runs := contiguousLevelRuns items0
  let mut items := items0
  let mut visited : Array Bool := Array.replicate runs.size false
  for r in [:runs.size] do
    if visited[r]! then
      continue
    let seq := runs[r]!
    if hseq : seq.size = 0 then
      continue
    else
      have hseq : 0 < seq.size := Nat.pos_of_ne_zero hseq
      let firstIndex := seq[0]'hseq
      let mut seq := seq
      let mut lastRun := r
      let mut lastRunSeq : {a : Array (Fin n) // 0 < a.size} := ⟨seq, hseq⟩
      visited := visited.set! r true
      let mut keepGoing := true
      while keepGoing do
        keepGoing := false
        let lastIndex := lastRunSeq.1[lastRunSeq.1.size - 1]'(by
          have hpos : 0 < lastRunSeq.1.size := lastRunSeq.2
          omega)
        let lastItem := items[lastIndex]
        if isIsolateInitiator lastItem.orig && lastItem.matchedIsolate then
          match findMatchingPdiIndex items lastItem.index with
          | some pdi =>
              match findRunStartingAt runs pdi with
              | some nextRun =>
                  if nextRun.val.val != lastRun && !visited[nextRun.val.val]! then
                    seq := seq ++ runs[nextRun.val]
                    lastRunSeq := ⟨runs[nextRun.val], nextRun.property⟩
                    visited := visited.set! nextRun.val.val true
                    lastRun := nextRun.val.val
                    keepGoing := true
              | none => pure ()
          | none => pure ()
      let lastIndex := lastRunSeq.1[lastRunSeq.1.size - 1]'(by
        have hpos : 0 < lastRunSeq.1.size := lastRunSeq.2
        omega)
      let level := items[firstIndex].level.getD paragraph
      let sot := dirClassOfLevel (max level (previousRunLevel runs r items paragraph))
      let eot := dirClassOfLevel (max (items[lastIndex].level.getD paragraph) (nextRunLevel runs lastRun items paragraph))
      items := resolveWeak sot seq items
      items := resolveBrackets sot seq items
      items := resolveNeutrals sot eot seq items
  return items

public def resolveImplicitLevels {n : Nat} (items0 : Vector Item n) : Vector Item n := Id.run do
  let mut items := items0
  let mut i := 0
  while h : i < n do
    match (items[i]).level with
    | none => pure ()
    | some level =>
        if isIsolateInitiator (items[i]).orig && !(items[i]).matchedIsolate then
          pure ()
        else
          let bc := (items[i]).cls
          let level :=
            if level % 2 == 0 then
              if bc == .rightToLeft then level + 1
              else if bc == .arabicNumber || bc == .europeanNumber then level + 2
              else level
            else
              if bc == .leftToRight || bc == .arabicNumber || bc == .europeanNumber then level + 1
              else level
          items := items.set i { items[i] with level := some level } h
    i := i + 1
  return items

end Unicode.BidiInternal
