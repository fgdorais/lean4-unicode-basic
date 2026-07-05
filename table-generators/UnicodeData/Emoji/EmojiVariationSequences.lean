/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `emoji-variation-sequences.txt` -/
def EmojiVariationSequences.txt := include_str "../../data-ucd/emoji/emoji-variation-sequences.txt"

/-- A raw emoji variation sequence record. -/
public structure EmojiVariationSequencesEntry where
  public sequence : Array UInt32
  public style : String
deriving Inhabited, Repr

/-- Parsed `emoji-variation-sequences.txt` records. -/
public def EmojiVariationSequences.data : Array EmojiVariationSequencesEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString EmojiVariationSequences.txt
  for record in stream do
    data := data.push {
      sequence := UCD.parseCodePointSequenceField record[0]!
      style := UCD.trimAsciiSlice record[1]!
    }
  return data

end Unicode
