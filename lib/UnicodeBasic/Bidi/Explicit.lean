/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi.Core

namespace Unicode.BidiInternal

public def resolveExplicitLevels (paragraph : Nat) (items0 : Array Item) : Vector Item items0.size := Id.run do
  let n := items0.size
  let mut items : Vector Item n := items0.toVector
  let mut stack : Array StackEntry := #[{ level := paragraph, override := .neutral, isolate := false, initiator := none }]
  let mut overflowIsolate := 0
  let mut overflowEmbedding := 0
  let mut validIsolate := 0
  let mut i := 0
  while h : i < n do
    let item := items[i]
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
            if firstStrongLevel items.toArray (i + 1) (match findMatchingPDI items.toArray i with | some j => j | none => n) == 0 then
              BidiClass.leftToRightIsolate
            else
              BidiClass.rightToLeftIsolate
          else
            item.orig
        items := items.set i { item with cls := applyOverride cur.override initiatorClass, level := some cur.level } h
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
              if hs : start < n then
                items := items.set start { items[start]'hs with matchedIsolate := true } hs
          | none => pure ()
          if stack.size > 1 then
            stack := stack.pop
          validIsolate := validIsolate - 1
        let cur := top! stack
        items := items.set i { item with cls := applyOverride cur.override item.orig, level := some cur.level, matchedPDI, matchingInitiator } h
    | .popDirectionalFormat =>
        if overflowIsolate > 0 then
          pure ()
        else if overflowEmbedding > 0 then
          overflowEmbedding := overflowEmbedding - 1
        else if !(top! stack).isolate && stack.size > 1 then
          stack := stack.pop
    | .paragraphSeparator =>
        items := items.set i { item with level := some paragraph } h
    | _ =>
        if !isRemovedByX9 item.orig then
          items := items.set i { item with cls := applyOverride cur.override item.orig, level := some cur.level } h
    i := i + 1
  -- X9 cleanup: remove explicit embedding/override/isolate controls
  i := 0
  while h : i < n do
    let item := items[i]
    if isRemovedByX9 item.orig then
      items := items.set i { item with level := none } h
    i := i + 1
  return items

public def previousInSeq? {n : Nat} (items : Vector Item n) (seq : Array (Fin n)) (pos : Nat) : Option BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    if h : j < seq.size then
      let bc := (items.get seq[j]).cls
      if !isRemovedByX9 bc then
        return some bc
  return none

public def nextInSeq? {n : Nat} (items : Vector Item n) (seq : Array (Fin n)) (pos : Nat) : Option BidiClass := Id.run do
  let mut j := pos + 1
  while h : j < seq.size do
    let bc := (items.get seq[j]).cls
    if !isRemovedByX9 bc then
      return some bc
    j := j + 1
  return none

@[inline] public def setClass {n : Nat} (items : Vector Item n) (i : Fin n) (bc : BidiClass) : Vector Item n :=
  items.set i.val { items.get i with cls := bc } i.isLt

public def prevStrongOrSot {n : Nat} (items : Vector Item n) (seq : Array (Fin n)) (pos : Nat) (sot : BidiClass) : BidiClass := Id.run do
  let mut j := pos
  while j > 0 do
    j := j - 1
    if h : j < seq.size then
      let bc := (items.get seq[j]).cls
      if isStrong bc then
        return bc
  return sot

end Unicode.BidiInternal
