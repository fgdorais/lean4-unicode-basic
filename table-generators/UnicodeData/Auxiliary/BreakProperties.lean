/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Type for break properties data -/
public structure BreakProperty where
  graphemeBreak : Array (UInt32 × Option UInt32 × String) := #[]
  wordBreak : Array (UInt32 × Option UInt32 × String) := #[]
  sentenceBreak : Array (UInt32 × Option UInt32 × String) := #[]
  lineBreak : Array (UInt32 × Option UInt32 × String) := #[]
deriving Inhabited, Repr

/-- Raw string from `GraphemeBreakProperty.txt` -/
public def GraphemeBreakProperty.txt := include_str "../../data-ucd/auxiliary/GraphemeBreakProperty.txt"
/-- Raw string from `WordBreakProperty.txt` -/
public def WordBreakProperty.txt := include_str "../../data-ucd/auxiliary/WordBreakProperty.txt"
/-- Raw string from `SentenceBreakProperty.txt` -/
public def SentenceBreakProperty.txt := include_str "../../data-ucd/auxiliary/SentenceBreakProperty.txt"
/-- Raw string from `LineBreak.txt` -/
public def LineBreak.txt := include_str "../../data-ucd/core/LineBreak.txt"

public unsafe initialize BreakProperties.data : BreakProperty ← do
  let mut list : BreakProperty := {}

  let streamG := UCDStream.ofString GraphemeBreakProperty.txt
  for record in streamG do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in GraphemeBreakProperty.txt"
    list := {list with graphemeBreak := list.graphemeBreak.push (val.1, val.2, record[1]!.copy)}

  let streamW := UCDStream.ofString WordBreakProperty.txt
  for record in streamW do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in WordBreakProperty.txt"
    list := {list with wordBreak := list.wordBreak.push (val.1, val.2, record[1]!.copy)}

  let streamS := UCDStream.ofString SentenceBreakProperty.txt
  for record in streamS do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in SentenceBreakProperty.txt"
    list := {list with sentenceBreak := list.sentenceBreak.push (val.1, val.2, record[1]!.copy)}

  let streamL := UCDStream.ofString LineBreak.txt
  for record in streamL do
    let val : UInt32 × Option UInt32 :=
      match record[0]!.split ".." |>.toList with
      | [c] => (ofHexString! c, none)
      | [c₀, c₁] => (ofHexString! c₀, some <| ofHexString! c₁)
      | _ => panic! "invalid record in LineBreak.txt"
    list := {list with lineBreak := list.lineBreak.push (val.1, val.2, record[1]!.copy)}

  return list

end Unicode
