/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.Bidi.Runs

namespace Unicode.BidiInternal

public def resetWhitespaceBefore (paragraph : Nat) (items0 : Array Item) (stop : Nat) : Array Item := Id.run do
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

public def resolveLineBreaks (paragraph : Nat) (items0 : Array Item) : Array Item := Id.run do
  let mut items := items0
  for i in [:items.size] do
    let bc := items[i]!.orig
    if bc == .segmentSeparator || bc == .paragraphSeparator then
      items := resetWhitespaceBefore paragraph items i
      if items[i]!.level.isSome then
        items := items.set! i { items[i]! with level := some paragraph }
  items := resetWhitespaceBefore paragraph items items.size
  return items

public def reverseSegment (order : Array Nat) (lo hi : Nat) : Array Nat := Id.run do
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

public def visualOrder (items : Array Item) : Array Nat := Id.run do
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

public def resolveItems (items0 : Array Item) (direction : Unicode.BidiParagraphDirection) : Unicode.BidiResolution :=
  let paragraph := paragraphLevel items0 direction
  let items := resolveExplicitLevels paragraph items0
  let items := resolveRuns paragraph items
  let items := resolveImplicitLevels items
  let items := resolveLineBreaks paragraph items.toArray
  {
    paragraphLevel := paragraph
    resolvedLevels := items.map (·.level)
    visualOrder := visualOrder items
  }

end Unicode.BidiInternal
