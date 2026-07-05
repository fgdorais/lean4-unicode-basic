module

namespace Unicode

private theorem and_15_lt_16 (code : UInt32) : (code &&& 0xF).toNat < 16 := by
  have h1 : (code &&& 0xF).toNat = code.toNat &&& 15 := rfl
  rw [h1]
  have h2 : code.toNat &&& 15 ≤ 15 := Nat.and_le_right
  omega

/-- Raw hexadecimal string representation of a code point

  Same as `toHexString` but without the `U+` prefix. -/
public def toHexStringRaw (code : UInt32) : String := Id.run do
  let hex := #['0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F']
  let mut code := code
  let mut dgts := []
  for _ in [:4] do
    have h : hex.size = 16 := rfl
    have h2 : (code &&& 0xF).toNat < hex.size := h ▸ and_15_lt_16 code
    dgts := hex[(code &&& 0xF).toNat]'h2 :: dgts
    code := code >>> 4
  while code != 0 do
    have h : hex.size = 16 := rfl
    have h2 : (code &&& 0xF).toNat < hex.size := h ▸ and_15_lt_16 code
    dgts := hex[(code &&& 0xF).toNat]'h2 :: dgts
    code := code >>> 4
  return String.ofList dgts

/-- Hexadecimal string representation of a code point

  Prefix `U+` followed by at least four uppercase hexadecimal digits
  (e.g. `U+0123` and `U+4B0A1` but neither `U+123` nor `U+4b0a1`).
-/
@[inline]
public def toHexString (code : UInt32) : String :=
  "U+" ++ toHexStringRaw code

/-- Get code point from hexadecimal string representation

  For convenience, the `U+` prefix may be omitted and lowercase hexadecimal
  digits are accepted.
-/
public def ofHexString? (str : String.Slice) : Option UInt32 := do
  let str := if str.take 2 == "U+" then str.drop 2 else str
  if str.isEmpty || str.utf8ByteSize > 8 then none else
    let mut val : UInt32 := 0
    for dgt in str.chars do
      val := (val <<< 4) + (← hexValue? dgt)
    some val

where

  @[inline] hexValue? (dgt : Char) : Option UInt32 := do
    if dgt.val < '0'.val then none else
      let mut n := dgt.val - '0'.val
      if n < 10 then
        some n
      else if dgt.val < 'A'.val then none else
        n := n - ('A'.val - '9'.val - 1)
        if n < 16 then
          some n
        else if dgt.val < 'a'.val then none else
          n := n - ('a'.val - 'A'.val)
          if n < 16 then
            some n
          else
            none

@[inherit_doc ofHexString?]
public def ofHexString! (str : String.Slice) : UInt32 :=
  match ofHexString? str with
  | some val => val
  | none => panic! "invalid unicode hexadecimal string representation"

end Unicode
