/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Structure containing supported emoji properties from `emoji-data.txt` -/
public structure EmojiData where
  public emoji : Array (UInt32 × Option UInt32) := #[]
  public emojiPresentation : Array (UInt32 × Option UInt32) := #[]
  public emojiModifier : Array (UInt32 × Option UInt32) := #[]
  public emojiModifierBase : Array (UInt32 × Option UInt32) := #[]
  public emojiComponent : Array (UInt32 × Option UInt32) := #[]
  public extendedPictographic : Array (UInt32 × Option UInt32) := #[]
deriving Inhabited, Repr

/-- Raw string form `emoji-data.txt` -/
protected def EmojiData.txt := include_str "../../data-ucd/emoji/emoji-data.txt"

public unsafe initialize EmojiData.data : EmojiData ←
  let stream := UCDStream.ofString EmojiData.txt
  let mut list : EmojiData := {}
  for record in stream do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in emoji-data.txt"
    if record[1]! == "Emoji" then
      list := {list with emoji := list.emoji.push val}
    if record[1]! == "Emoji_Presentation" then
      list := {list with emojiPresentation := list.emojiPresentation.push val}
    if record[1]! == "Emoji_Modifier" then
      list := {list with emojiModifier := list.emojiModifier.push val}
    if record[1]! == "Emoji_Modifier_Base" then
      list := {list with emojiModifierBase := list.emojiModifierBase.push val}
    if record[1]! == "Emoji_Component" then
      list := {list with emojiComponent := list.emojiComponent.push val}
    if record[1]! == "Extended_Pictographic" then
      list := {list with extendedPictographic := list.extendedPictographic.push val}
  return list

-- TODO: stop reinventing the wheel!
/-- Binary search -/
private partial def find (code : UInt32) (data : Array (UInt32 × Option UInt32)) (lo hi : Nat) : Nat :=
  assert! (hi ≤ data.size)
  assert! (lo < hi)
  assert! (data[lo]!.fst ≤ code)
  let mid := (lo + hi) / 2 -- NB: mid < hi because lo < hi
  if lo = mid then
    mid
  else
    if code < data[mid]!.fst then
      find code data lo mid
    else
      find code data mid hi

@[inline]
public def EmojiData.isEmoji (code : UInt32) : Bool :=
  let data := EmojiData.data.emoji
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

@[inline]
public def EmojiData.isEmojiPresentation (code : UInt32) : Bool :=
  let data := EmojiData.data.emojiPresentation
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

@[inline]
public def EmojiData.isEmojiModifier (code : UInt32) : Bool :=
  let data := EmojiData.data.emojiModifier
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

@[inline]
public def EmojiData.isEmojiModifierBase (code : UInt32) : Bool :=
  let data := EmojiData.data.emojiModifierBase
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

@[inline]
public def EmojiData.isEmojiComponent (code : UInt32) : Bool :=
  let data := EmojiData.data.emojiComponent
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

@[inline]
public def EmojiData.isExtendedPictographic (code : UInt32) : Bool :=
  let data := EmojiData.data.extendedPictographic
  if data.size == 0 || code < data[0]!.fst then false else
    match data[find code data 0 data.size]! with
    | (val, none) => code == val
    | (_, some top) => code <= top

end Unicode
