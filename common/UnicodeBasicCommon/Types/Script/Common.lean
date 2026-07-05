module

namespace Unicode.Script.Common

/-- Get the raw `UInt32` script code point from an abbreviation slice.
    Returns `some code` if the slice is exactly 4 bytes, otherwise `none`. -/
@[inline]
public def ofAbbrevAux (abbr : String.Slice) : Option UInt32 :=
  let b := abbr.str.toUTF8
  let off := abbr.startInclusive.offset.byteIdx
  let stop := abbr.endExclusive.offset.byteIdx
  -- Ensure the slice is exactly 4 bytes AND within the bounds of the source string
  if h : off + 4 = stop ∧ stop <= b.size then
    -- Indices are safe because off + 4 = stop and stop <= b.size
    let b0 := b[off]'(by omega)
    let b1 := b[off + 1]'(by omega)
    let b2 := b[off + 2]'(by omega)
    let b3 := b[off + 3]'(by omega)

    let code : UInt32 :=
      (b0.toUInt32 <<< 24) |||
      (b1.toUInt32 <<< 16) |||
      (b2.toUInt32 <<< 8)  |||
       b3.toUInt32
    some code
  else
    none

/-- String abbreviation of script -/
@[inline]
public def toAbbrevImpl (c : UInt32) : String :=
  let c0 := Char.ofUInt8 (c >>> 24).toUInt8
  let c1 := Char.ofUInt8 (c >>> 16).toUInt8
  let c2 := Char.ofUInt8 (c >>> 8).toUInt8
  let c3 := Char.ofUInt8 c.toUInt8
  String.ofList [c0, c1, c2, c3]
