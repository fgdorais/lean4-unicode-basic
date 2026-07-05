/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
import UnicodeData.UcdParse

namespace Unicode

/-- Raw string from `EmojiSources.txt` -/
def EmojiSources.txt := include_str "../../data-ucd/core/EmojiSources.txt"

/-- A raw emoji source record. -/
public structure EmojiSourcesEntry where
  public unicode : Array UInt32
  public docomo : String
  public kddi : String
  public softbank : String
deriving Inhabited, Repr

/-- Parsed `EmojiSources.txt` records. -/
public def EmojiSources.data : Array EmojiSourcesEntry := Id.run do
  let mut data := #[]
  let stream := UCDStream.ofString EmojiSources.txt
  for record in stream do
    data := data.push {
      unicode := UCD.parseCodePointSequenceField record[0]!
      docomo := UCD.trimAsciiSlice record[1]!
      kddi := UCD.trimAsciiSlice record[2]!
      softbank := UCD.trimAsciiSlice record[3]!
    }
  return data

end Unicode
