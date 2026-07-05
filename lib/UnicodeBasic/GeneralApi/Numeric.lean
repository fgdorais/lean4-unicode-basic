/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.NumericValue

/-!
  This file uses lookup tables:
  `NumericValue`.
  It also contains inline data extracted from `PropList.txt` for `Hex_Digit`
  and inline numeric code point lists for `Numeric_Type=Numeric`.
-/

namespace Unicode

/-!
  ## Numeric Type and Value ##
-/

/-- Check if character represents a numerical value

  Unicode property: `Numeric_Type=Numeric` -/
@[inline]
public def isNumeric (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some _ => true
    | _ => otherNumeric.elem char.val
where
  -- Extracted
  otherNumeric := #[
    0x3405, 0x3483, 0x382A, 0x3B4D, 0x4E00, 0x4E03, 0x4E07, 0x4E09, 0x4E5D, 0x4E8C,
    0x4E94, 0x4E96, 0x4EBF, 0x4EC0, 0x4EDF, 0x4EE8, 0x4F0D, 0x4F70, 0x5104, 0x5146,
    0x5169, 0x516B, 0x516D, 0x5341, 0x5343, 0x5344, 0x5345, 0x534C, 0x53C1, 0x53C2,
    0x53C3, 0x53C4, 0x56DB, 0x58F1, 0x58F9, 0x5E7A, 0x5EFE, 0x5EFF, 0x5F0C, 0x5F0D,
    0x5F0E, 0x5F10, 0x62FE, 0x634C, 0x67D2, 0x6F06, 0x7396, 0x767E, 0x8086, 0x842C,
    0x8CAE, 0x8CB3, 0x8D30, 0x9621, 0x9646, 0x964C, 0x9678, 0x96F6, 0xF96B, 0xF973,
    0xF978, 0xF9B2, 0xF9D1, 0xF9D3, 0xF9FD, 0x20001, 0x20064, 0x200E2, 0x20121, 0x2092A,
    0x20983, 0x2098C, 0x2099C, 0x20AEA, 0x20AFD, 0x20B19, 0x22390, 0x22998, 0x23B1B, 0x2626D,
    0x2F890]

/-- Check if character represents a digit in base 10

  Unicode property: `Numeric_Type=Digit` -/
@[inline]
public def isDigit (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | some (.digit _) => true
    | _ => false

/-- Get value of digit

  Unicode properties:
    `Numeric_Type=Digit`
    `Numeric_Value` -/
@[inline]
public def getDigit? (char : Char) : Option (Fin 10) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char.toNat < '0'.toNat then
      none
    else
      let n := char.toNat - '0'.toNat
      if h : n < 10 then
        some ⟨n, h⟩
      else
        none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) => some value
    | some (.digit value) => some value
    | _ => none

/-- Check if character represents a decimal digit

  For this property, a character must be part of a contiguous sequence
  representing the ten decimal digits in order from 0 to 9.

  Unicode property: `Numeric_Type=Decimal` -/
@[inline]
public def isDecimal (char : Char) : Bool :=
  -- ASCII shortcut
  if char.val < 0x80 then
    char >= '0' && char <= '9'
  else
    match lookupNumericValue char.val with
    | some (.decimal _) => true
    | _ => false

/-- Get decimal digit range

  If the character is part of a contiguous sequence representing the ten
  decimal digits in order from 0 to 9, this function returns the first and
  last characters from this range.

  Unicode properties:
    `Numeric_Type=Decimal`
    `Numeric_Value` -/
@[inline]
public def getDecimalRange? (char : Char) : Option (Char × Char) :=
  -- ASCII shortcut
  if char.val < 0x80 then
    if char >= '0' && char <= '9' then
      some ('0', '9')
    else
      none
  else
    match lookupNumericValue char.val with
    | some (.decimal value) =>
      let first := char.toNat - value.val
      some (Char.ofNat first, Char.ofNat (first + 9))
    | _ => none

/-- Check if character represents a hexadecimal digit

  Unicode property: `Hex_Digit` -/
@[inline]
public def isHexDigit (char : Char) : Bool :=
  -- Extracted from `PropList.txt`
  char.val <= 0x0039 && char.val >= 0x0030 || -- [10] DIGIT ZERO..DIGIT NINE
  char.val <= 0x0046 && char.val >= 0x0041 || --  [6] LATIN CAPITAL LETTER A..LATIN CAPITAL LETTER F
  char.val <= 0x0066 && char.val >= 0x0061 || --  [6] LATIN SMALL LETTER A..LATIN SMALL LETTER F
  char.val <= 0xFF19 && char.val >= 0xFF10 || -- [10] FULLWIDTH DIGIT ZERO..FULLWIDTH DIGIT NINE
  char.val <= 0xFF26 && char.val >= 0xFF21 || --  [6] FULLWIDTH LATIN CAPITAL LETTER A..FULLWIDTH LATIN CAPITAL LETTER F
  char.val <= 0xFF46 && char.val >= 0xFF41    --  [6] FULLWIDTH LATIN SMALL LETTER A..FULLWIDTH LATIN SMALL LETTER F

/-- Get value of a hexadecimal digit

  Unicode property: `Hex_Digit` -/
@[inline]
public def getHexDigit? (char : Char) : Option (Fin 16) :=
  if char.toNat < 0x30 then
    none
  else
    let n := if char.toNat < 0xFF10 then char.toNat - 0x0030 else char.toNat - 0xFF10
    if h : n < 10 then
      some ⟨n, Nat.lt_trans h (by decide)⟩
    else if n >= 17 then
      let n := n - 7
      if h : n < 16 then
        some ⟨n, h⟩
      else if n >= 32 then
        if h : n - 32 < 16 then
          some ⟨n - 32, h⟩
        else
          none
      else
        none
    else
      none

end Unicode
