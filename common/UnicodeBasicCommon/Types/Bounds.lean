module

/-- Low-level conversion from `UInt32` to `Char` (*unsafe*)

  This function translates to a no-op in the compiler. However, it does not
  check whether the `UInt32` code is a valid `Char` value. Only use where it's
  known for external reasons that the code is valid. -/
public protected unsafe def Char.mkUnsafe : UInt32 → Char := unsafeCast

namespace Unicode

/-- Maximum valid code point value -/
@[simp, grind =]
public protected abbrev max : UInt32 := 0x10FFFF

/-- Minimum high surrogate code point -/
@[simp, grind =]
public protected abbrev minHighSurrogate : UInt32 := 0xD800

/-- Maximum high surrogate code point -/
@[simp, grind =]
public protected abbrev maxHighSurrogate : UInt32 := 0xDBFF

/-- Minimum low surrogate code point -/
@[simp, grind =]
public protected abbrev minLowSurrogate : UInt32 := 0xDC00

/-- Maximum low surrogate code point -/
@[simp, grind =]
public protected abbrev maxLowSurrogate : UInt32 := 0xDFFF

/-- Minimum surrogate code point -/
@[simp, grind =]
public protected abbrev minSurrogate : UInt32 := Unicode.minHighSurrogate

/-- Minimum surrogate code point -/
@[simp, grind =]
public protected abbrev maxSurrogate : UInt32 := Unicode.maxLowSurrogate
