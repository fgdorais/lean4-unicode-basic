/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Hangul
public import UnicodeBasic.Internal.BidiClassTree
public import UnicodeBasic.Internal.BidiMirroredTree
public import UnicodeBasic.Internal.CaseFoldingTree
public import UnicodeBasic.Internal.CaseTree
public import UnicodeBasic.Internal.CombiningClassTree
public import UnicodeBasic.Internal.DecompositionTree
public import UnicodeBasic.Internal.DefaultIgnorableTree
public import UnicodeBasic.Internal.NumericTree
public import UnicodeBasic.Internal.PropTree
public import UnicodeBasic.Internal.ScriptTree
public import UnicodeBasic.Types

/-! # Table lookups

The functions in this module are not part of the public API and may change at
any time. Use the functions in `UnicodeBasic` instead.
-/

namespace Unicode

namespace CLib

/-- Data of a code point, looked up in the B-tree `t` with data `width` bits wide, or `default`
(internal use only) -/
@[expose] public protected def lookupIn (t : Internal.BTree Nat) (width default c : Nat) :
    UInt64 :=
  match t.find? c with
  | none => default.toUInt64
  | some (block, k) => (block >>> (width * k) &&& (1 <<< width) - 1).toUInt64

/-- Bidi classes, in the order of their codes in `CLib.lookupBidiClass` (internal use only) -/
@[expose] public protected def bidiClasses : Array BidiClass := #[
  .leftToRight, .rightToLeft, .arabicLetter, .europeanNumber, .europeanSeparator,
  .europeanTerminator, .arabicNumber, .commonSeparator, .nonspacingMark, .boundaryNeutral,
  .paragraphSeparator, .segmentSeparator, .whiteSpace, .otherNeutral, .leftToRightEmbedding,
  .leftToRightOverride, .rightToLeftEmbedding, .rightToLeftOverride, .popDirectionalFormat,
  .leftToRightIsolate, .rightToLeftIsolate, .firstStrongIsolate, .popDirectionalIsolate]

/-- Code of the bidi class of a code point, looked up in the B-tree `t` (internal use only) -/
@[expose] public protected def lookupBidiClassIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  CLib.lookupIn t 5 9 c -- default BN

/-- Code of the bidi class of a code point, an index into `CLib.bidiClasses` (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.BidiClassTree`. `util/TestTables` checks that the two agree on every
-- code point.
@[extern "unicode_bidi_class_lookup", expose]
public protected def lookupBidiClass (c : UInt32) : UInt64 :=
  CLib.lookupBidiClassIn Internal.bidiClassTree c.toNat

/-- `1` if a code point is bidi mirrored, `0` otherwise, looked up in the B-tree `t` (internal
use only) -/
@[expose] public protected def lookupBidiMirroredIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  CLib.lookupIn t 1 0 c

/-- `1` if a code point is bidi mirrored, `0` otherwise (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.BidiMirroredTree`. `util/TestTables` checks that the two agree on every
-- code point.
@[extern "unicode_bidi_mirrored_lookup", expose]
public protected def lookupBidiMirrored (c : UInt32) : UInt64 :=
  CLib.lookupBidiMirroredIn Internal.bidiMirroredTree c.toNat

/-- Canonical combining class of a code point, looked up in the B-tree `t` (internal use only) -/
@[expose] public protected def lookupCombiningClassIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  CLib.lookupIn t 8 0 c

/-- Canonical combining class of a code point (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.CombiningClassTree`. `util/TestTables` checks that the two agree on
-- every code point.
@[extern "unicode_combining_class_lookup", expose]
public protected def lookupCombiningClass (c : UInt32) : UInt64 :=
  CLib.lookupCombiningClassIn Internal.combiningClassTree c.toNat

/-- `1` if a code point is default ignorable, `0` otherwise, looked up in the B-tree `t`
(internal use only) -/
@[expose] public protected def lookupDefaultIgnorableIn (t : Internal.BTree Nat) (c : Nat) :
    UInt64 :=
  CLib.lookupIn t 1 0 c

/-- `1` if a code point is default ignorable, `0` otherwise (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.DefaultIgnorableTree`. `util/TestTables` checks that the two agree on
-- every code point.
@[extern "unicode_default_ignorable_lookup", expose]
public protected def lookupDefaultIgnorable (c : UInt32) : UInt64 :=
  CLib.lookupDefaultIgnorableIn Internal.defaultIgnorableTree c.toNat

/-- Encoded numeric type and value of a code point, looked up in the B-tree `t` (internal use
only) -/
@[expose] public protected def lookupNumericIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  CLib.lookupIn t 52 0 c

/-- Encoded numeric type and value of a code point, see `UnicodeCLib/numeric.c` (internal use
only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.NumericTree`. `util/TestTables` checks that the two agree on every code
-- point.
@[extern "unicode_numeric_lookup", expose]
public protected def lookupNumeric (c : UInt32) : UInt64 :=
  CLib.lookupNumericIn Internal.numericTree c.toNat

/-- Simple case mappings of a code point, looked up in the B-tree `t` (internal use only) -/
@[expose] public protected def lookupCaseIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  match t.find? c with
  | none => 0
  | some (block, k) => (block >>> (63 * k) &&& 0x7FFFFFFFFFFFFFFF).toUInt64

/-- Simple case mappings of a code point (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.CaseTree`. `util/TestTables` checks that the two agree on every code
-- point.
@[extern "unicode_case_lookup", expose]
public protected def lookupCase (c : UInt32) : UInt64 :=
  CLib.lookupCaseIn Internal.caseTree c.toNat

/-- `Other_Uppercase` bit of `CLib.lookupProp` (internal use only) -/
public protected abbrev oUpper : UInt64 := 0x100000000
/-- `Other_Lowercase` bit of `CLib.lookupProp` (internal use only) -/
public protected abbrev oLower : UInt64 := 0x200000000
/-- `Other_Alphabetic` bit of `CLib.lookupProp` (internal use only) -/
public protected abbrev oAlpha : UInt64 := 0x400000000
/-- `Other_Math` bit of `CLib.lookupProp` (internal use only) -/
public protected abbrev oMath  : UInt64 := 0x800000000

/-- General category and `Other_*` property bits of a code point, looked up in the B-tree `t`
(internal use only) -/
@[expose] public protected def lookupPropIn (t : Internal.BTree Nat) (c : Nat) : UInt64 :=
  match t.find? c with
  | none => 0x20000000 -- Cn
  | some (block, k) =>
    let d := block >>> (36 * k) &&& 0xFFFFFFFFF
    let gc := d &&& 0x3FFFFFFF
    let pb := d >>> 31 &&& 1
    let op := d &&& 0xF00000000
    -- Alternating pairs, see `UnicodeCLib/prop.c`
    let gc :=
      if gc == 0x7 then -- LC
        if c % 2 == pb then 0x1 else 0x2 -- Lu, Ll
      else if gc == 0x6000 then -- PG
        if c % 2 == pb then 0x2000 else 0x4000 -- Ps, Pe
      else if gc == 0x18000 then -- PQ
        if c % 2 == pb then 0x8000 else 0x10000 -- Pi, Pf
      else gc
    (op ||| gc).toUInt64

/-- General category and `Other_*` property bits of a code point (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.PropTree`. `util/TestTables` checks that the two agree on every code
-- point.
@[extern "unicode_prop_lookup", expose]
public protected def lookupProp (c : UInt32) : UInt64 :=
  CLib.lookupPropIn Internal.propTree c.toNat

/-- Script of a code point, looked up in the B-tree `t` (internal use only) -/
@[expose] public protected def lookupScriptIn (t : Internal.BTree Nat) (c : Nat) : Script :=
  let v : UInt32 :=
    match t.find? c with
    | none => (default : Script).code -- Zzzz
    | some (block, k) => (block >>> (32 * k) &&& 0xFFFFFFFF).toUInt32
  if h : Script.isValid v then ⟨v, h⟩ else default

/-- Script of a code point (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.ScriptTree`. `util/TestTables` checks that the two agree on every code
-- point.
@[extern "unicode_script_lookup", expose]
public protected def lookupScript (c : UInt32) : Script :=
  CLib.lookupScriptIn Internal.scriptTree c.toNat

/-- Data of a code point, looked up in the B-tree `t` with data `width` bits wide, or `0`, as a
`Nat` (internal use only) -/
@[expose] public protected def lookupWideIn (t : Internal.BTree Nat) (width c : Nat) : Nat :=
  match t.find? c with
  | none => 0
  | some (block, k) => block >>> (width * k) &&& (1 <<< width) - 1

/-- Encoded case foldings of a code point, looked up in the B-tree `t` (internal use only) -/
@[expose] public protected def lookupCaseFoldingIn (t : Internal.BTree Nat) (c : Nat) : Nat :=
  CLib.lookupWideIn t 85 c

/-- Low 64 bits of the encoded case foldings of a code point, see `UnicodeCLib/case_folding.c`
(internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.CaseFoldingTree`. `util/TestTables` checks that the two agree on every
-- code point.
@[extern "unicode_case_folding_lookup_lo", expose]
public protected def lookupCaseFoldingLo (c : UInt32) : UInt64 :=
  (CLib.lookupCaseFoldingIn Internal.caseFoldingTree c.toNat).toUInt64

/-- High 64 bits of the encoded case foldings of a code point, see `UnicodeCLib/case_folding.c`
(internal use only) -/
-- Compiled code calls the C table, as for `CLib.lookupCaseFoldingLo`.
@[extern "unicode_case_folding_lookup_hi", expose]
public protected def lookupCaseFoldingHi (c : UInt32) : UInt64 :=
  (CLib.lookupCaseFoldingIn Internal.caseFoldingTree c.toNat >>> 64).toUInt64

/-- Encoded canonical decomposition of a code point, looked up in the B-tree `t` (internal use
only) -/
@[expose] public protected def lookupDecompositionIn (t : Internal.BTree Nat) (c : Nat) : Nat :=
  CLib.lookupWideIn t 84 c

/-- Low 64 bits of the encoded canonical decomposition of a code point, see
`UnicodeCLib/decomposition.c` (internal use only) -/
-- Compiled code calls the C table. The kernel unfolds the body, which reads the same data from
-- `UnicodeBasic.Internal.DecompositionTree`. `util/TestTables` checks that the two agree on every
-- code point.
@[extern "unicode_decomposition_lookup_lo", expose]
public protected def lookupDecompositionLo (c : UInt32) : UInt64 :=
  (CLib.lookupDecompositionIn Internal.decompositionTree c.toNat).toUInt64

/-- High 64 bits of the encoded canonical decomposition of a code point, see
`UnicodeCLib/decomposition.c` (internal use only) -/
-- Compiled code calls the C table, as for `CLib.lookupDecompositionLo`.
@[extern "unicode_decomposition_lookup_hi", expose]
public protected def lookupDecompositionHi (c : UInt32) : UInt64 :=
  (CLib.lookupDecompositionIn Internal.decompositionTree c.toNat >>> 64).toUInt64

/-- Code points packed 21 bits each in `d`, up to the first `0`, at most `n` of them (internal
use only) -/
@[expose] public protected def unpackCodes (d : Nat) : (n : Nat) → List UInt32
  | 0 => []
  | n + 1 =>
    let x := d &&& 0x1FFFFF
    if x == 0 then [] else x.toUInt32 :: CLib.unpackCodes (d >>> 21) n

end CLib

/-- Binary search -/
@[specialize]
private partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

/-- Parse a simple table -/
private def parseTable (s : String) (f : UInt32 → Array String.Slice → α) : Thunk <| Array (UInt32 × α) :=
  .mk fun _ => Id.run do
    let mut r := #[]
    let mut stream := UCDStream.ofString s
    for record in stream do
      let start := ofHexString! record[0]!
      let val := f start record[1:]
      r := r.push (start, val)
    return r

/-- Parse a range compressed data table -/
private def parseDataTable (s : String) (f : UInt32 → UInt32 → Array String.Slice → α) : Thunk <| Array (UInt32 × UInt32 × α) :=
  .mk fun _ => Id.run do
    let mut r := #[]
    let mut stream := UCDStream.ofString s
    for record in stream do
      let start := ofHexString! record[0]!
      let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
      let val := f start stop record[2:]
      r := r.push (start, stop, val)
    return r

/-- Get bidirectional class using lookup table

  Unicode property: `Bidi_Class` -/
@[expose]
public def lookupBidiClass (c : UInt32) : BidiClass :=
  CLib.bidiClasses.getD (CLib.lookupBidiClass c).toNat .boundaryNeutral

/-- Get canonical combining class using lookup table

  Unicode property: `Canonical_Combining_Class` -/
@[expose]
public def lookupCanonicalCombiningClass (c : UInt32) : Nat :=
  (CLib.lookupCombiningClass c).toNat

/-- Get canonical decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
@[expose]
public def lookupCanonicalDecompositionMapping (c : UInt32) : List UInt32 :=
  -- Hangul syllables, by the algorithm in Section 3.12 of the Standard
  if 0xAC00 ≤ c && c ≤ 0xD7A3 then
    let i := c - 0xAC00
    let l := 0x1100 + i / 588
    let v := 0x1161 + i % 588 / 28
    let t := i % 28
    if t == 0 then [l, v] else [l, v, 0x11A7 + t]
  else
    let lo := CLib.lookupDecompositionLo c
    if lo == 0 then [c] else
      CLib.unpackCodes (lo.toNat ||| (CLib.lookupDecompositionHi c).toNat <<< 64) 4

/-- Get simple and full case foldings of a code point using lookup table

  Returns `(s, f)` where `s` is the simple case folding, or `none` if the code
  point folds to itself, and `f` is the full case folding, or `[]` if it agrees
  with the simple case folding.

  Unicode properties:
    `Case_Folding`
    `Simple_Case_Folding` -/
@[expose, inline]
public def lookupCaseFolding (c : UInt32) : Option UInt32 × List UInt32 :=
  let lo := CLib.lookupCaseFoldingLo c
  let s := lo &&& 0x3FFFFF
  let s := if s == 0 then none else some ((c.toUInt64 + s) % 0x400000).toUInt32
  if lo >>> 22 == 0 then (s, []) else
    (s, CLib.unpackCodes (lo.toNat >>> 22 ||| (CLib.lookupCaseFoldingHi c).toNat <<< 42) 3)

/-- Get simple case mappings of a code point using lookup table

  Unicode properties:
    `Simple_Lowercase_Mapping`
    `Simple_Uppercase_Mapping`
    `Simple_Titlecase_Mapping` -/
@[expose, inline]
public def lookupCaseMapping (c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let v : UInt64 := CLib.lookupCase c
  if v == 0 then (c, c, c) else
    let cu : UInt32 := v.toUInt32 &&& 0x001FFFFF
    let cl : UInt32 := (v >>> 21).toUInt32 &&& 0x001FFFFF
    let ct : UInt32 := (v >>> 42).toUInt32 &&& 0x001FFFFF
    (cu, cl, ct)

/-- Get full case mappings of a code point using lookup table

  Returns `(l, t, u)` where `l` is the full lowercase mapping, or `[]` if it
  agrees with the simple lowercase mapping, and similarly `t` for titlecase and
  `u` for uppercase. Only unconditional mappings are included.

  Unicode properties:
    `Lowercase_Mapping`
    `Titlecase_Mapping`
    `Uppercase_Mapping` -/
public def lookupSpecialCasing (c : UInt32) : List UInt32 × List UInt32 × List UInt32 :=
  let t := table.get
  if c < t[0]!.1 then ([], [], []) else
    match t[find c (fun i => t[i]!.1) 0 t.size.toUSize]! with
    | (c', v) => if c == c' then v else ([], [], [])
where
  str : String := include_str "../data/Special_Casing.txt"
  table : Thunk <| Array (UInt32 × List UInt32 × List UInt32 × List UInt32) :=
    parseTable str fun _ x =>
      let parse (s : String.Slice) : List UInt32 :=
        if s.isEmpty then [] else s.split " " |>.toList.map ofHexString!
      (parse x[0]!, parse x[1]!, parse x[2]!)

/-- Get decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type` -/
public def lookupDecompositionMapping? (c : UInt32) : Option DecompositionMapping :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => some ⟨none, [s.getLVChar, t]⟩
    | none => some ⟨none, [s.getLChar, s.getVChar]⟩
  else
    let table := table.get
    if c < table[0]!.1 then none else
      match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
      | (v, m) => if c == v then m else none
where
  str : String := include_str "../data/Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × Option DecompositionMapping) :=
    parseTable str fun _ x =>
      let tag :=
        if x[0]! == "" then none
        else if x[0]! == "<font>" then some .font
        else if x[0]! == "<noBreak>" then some .noBreak
        else if x[0]! == "<initial>" then some .initial
        else if x[0]! == "<medial>" then some .medial
        else if x[0]! == "<final>" then some .final
        else if x[0]! == "<isolated>" then some .isolated
        else if x[0]! == "<circle>" then some .circle
        else if x[0]! == "<super>" then some .super
        else if x[0]! == "<sub>" then some .sub
        else if x[0]! == "<vertical>" then some .vertical
        else if x[0]! == "<wide>" then some .wide
        else if x[0]! == "<narrow>" then some .narrow
        else if x[0]! == "<small>" then some .small
        else if x[0]! == "<square>" then some .square
        else if x[0]! == "<fraction>" then some .fraction
        else if x[0]! == "<compat>" then some .compat
        else panic! s!"invalid compatibility tag {x[0]!.copy}"
      some ⟨tag, x[1:].toArray.toList.map fun s => Char.ofNat (ofHexString! s).toNat⟩

/-- Get general category of a code point using lookup table

  Unicode property: `General_Category` -/
@[expose, inline]
public def lookupGC (c : UInt32) : GC := CLib.lookupProp c |>.toUInt32

/-- Get name of a code point using lookup table

  Unicode property: `Name` -/
public def lookupName (c : UInt32) : String :=
  let table := table.get
  if c < table[0]!.1 then unreachable! else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, d) =>
      if c ≤ v then
        if Char.ofUInt8 (d.getUTF8Byte! 0) == '<' then
          if d == "<control>" then
            s!"<control-{toHexStringRaw c}>"
          else if d == "<private use>" then
            s!"<private-use-{toHexStringRaw c}>"
          else if d == "<noncharacter>" then
            s!"<noncharacter-{toHexStringRaw c}>"
          else if d == "<surrogate>" then
            s!"<surrogate-{toHexStringRaw c}>"
          else if d == "<cjk unified ideograph>" then
            "CJK UNIFIED IDEOGRAPH-" ++ toHexStringRaw c
          else if d == "<cjk compatibility ideograph>" then
            "CJK COMPATIBILITY IDEOGRAPH-" ++ toHexStringRaw c
          else if d == "<hangul syllable>" then
            "HANGUL SYLLABLE " ++ (Hangul.getSyllable! c).getShortName
          else if d == "<khitan small script character>" then
            "KHITAN SMALL SCRIPT CHARACTER-" ++ toHexStringRaw c
          else if d == "<egyptian hieroglyph>" then
            "EGYPTIAN HIEROGLYPH-" ++ toHexStringRaw c
          else if d == "<nushu character>" then
            "NUSHU CHARACTER-" ++ toHexStringRaw c
          else if d == "<tangut component>" then
            let i := if c.toNat < 0x18B00 then
                -- Tangut Component
                toString <| c.toNat - 0x18800 + 1
              else
                -- Tangut Component Supplement
                toString <| c.toNat - 0x18D80 + 769
            let i :=
              if i.length == 1 then "00" ++ i
              else if i.length == 2 then "0" ++ i
              else i
            "TANGUT COMPONENT-" ++ i
          else if d == "<tangut ideograph>" then
            "TANGUT IDEOGRAPH-" ++ toHexStringRaw c
          else if d == "<jurchen character>" then
            "JURCHEN CHARACTER-" ++ toHexStringRaw c
          else if d == "<seal character>" then
            "SMALL SEAL CHARACTER-" ++ toHexStringRaw c
          else panic! s!"unknown name range {d.copy}"
        else String.Slice.copy d
      else s!"<reserved-{toHexStringRaw c}>"
where
  str : String := include_str "../data/Name.txt"
  table : Thunk <| Array (UInt32 × UInt32 × String.Slice) :=
    parseDataTable str fun _ _ x => x[0]!

/-- Get numeric value of a code point using lookup table

  Unicode properties:
    `Numeric_Type`
    `Numeric_Value` -/
@[expose]
public def lookupNumericValue (c : UInt32) : Option NumericType :=
  let d := (CLib.lookupNumeric c).toNat
  let tag := d &&& 0x3
  if tag == 0 then none
  else if tag == 3 then
    let num : Int := d >>> 12
    let den := d >>> 3 &&& 0x1FF
    some <| .numeric (if d &&& 0x4 == 0 then num else -num) (if den == 0 then none else some den)
  else
    -- decimal and digit ranges: first code point and its value
    let val := c.toNat - (d >>> 2 &&& 0x1FFFFF) + (d >>> 23 &&& 0xF)
    if h : val < 10 then
      some <| if tag == 1 then .decimal ⟨val, h⟩ else .digit ⟨val, h⟩
    else none

/-- Get other properties using lookup table

  Unicode properties: `Other_Alphabetic`, `Other_Lowercase`, `Other_Uppercase`, `Other_Math` -/
public def lookupOther (c : UInt32) : UInt32 :=
  CLib.lookupProp c >>> 32 |>.toUInt32

/-! Properties -/

/-- Check if code point is alphabetic using lookup table

  Unicode property: `Alphabetic` -/
@[expose, inline]
public def lookupAlphabetic (c : UInt32) : Bool :=
  let m := CLib.oAlpha ||| (GC.L ||| GC.Nl).toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is bidi mirrored using lookup table

  Unicode property: `Bidi_Mirrored`
-/
@[expose]
public def lookupBidiMirrored (c : UInt32) : Bool :=
  CLib.lookupBidiMirrored c != 0

/-- Check if code point is a cased letter using lookup table

  Unicode property: `Cased` -/
@[expose, inline]
public def lookupCased (c : UInt32 ) : Bool :=
  let m := CLib.oUpper ||| CLib.oLower ||| GC.LC.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is ignorable using lookup table

  Unicode property: `Default_Ignorable_Code_Point` -/
@[expose, inline]
public def lookupDefaultIgnorableCodePoint (c : UInt32) : Bool :=
  CLib.lookupDefaultIgnorable c != 0

/-- Check if code point is a lowercase letter using lookup table

  Unicode property: `Lowercase` -/
@[expose, inline]
public def lookupLowercase (c : UInt32) : Bool :=
  let m := CLib.oLower ||| GC.Ll.toUInt64
  CLib.lookupProp c &&& m != 0


/-- Check if code point is a mathematical symbol using lookup table

  Unicode property: `Math` -/
@[expose, inline]
public def lookupMath (c : UInt32) : Bool :=
  let m := CLib.oMath ||| GC.Sm.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Check if code point is a noncharacter code point

  Unicode property: `Noncharacter_Code_Point` -/
@[expose, inline]
public def lookupNoncharacterCodePoint (c : UInt32) : Bool :=
  (c ≤ 0xFDEF && 0xFDD0 ≤ c) || (c ≤ Unicode.max && c &&& 0xFFFE == 0xFFFE)

/-- Check if code point is a titlecase letter using lookup table

  Unicode property: `Titlecase` -/
@[inline]
public def lookupTitlecase (c : UInt32) : Bool :=
  lookupGC c == GC.Lt

/-- Check if code point is an uppercase letter using lookup table

  Unicode property: `Uppercase` -/
@[expose, inline]
public def lookupUppercase (c : UInt32) : Bool :=
  let m := CLib.oUpper ||| GC.Lu.toUInt64
  CLib.lookupProp c &&& m != 0

/-- Get the script of a code point using lookup table

  Unicode property: `Script` -/
@[expose, inline]
public def lookupScript (c : UInt32) : Script := CLib.lookupScript c

/-- Get the name of a script

  Unicode property: `Script` -/
public def lookupScriptName (s : Script) : Option String :=
  let table := table.get
  if s.code < table[0]!.1 then none else
    match table[find s.code (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (c, v) => if s.code = c then v else none
where
  str : String := include_str "../data/Script_Name.txt"
  table : Thunk <| Array (UInt32 × Option String) := parseTable str fun _ n => some n[0]!.copy

/-- Get the set of scripts a code point is commonly used with, using lookup table

  Unicode property: `Script_Extensions` -/
public def lookupScriptSet (c : UInt32) : ScriptSet :=
  let table := table.get
  if c < table[0]!.1 then ⟨#[lookupScript c], rfl⟩ else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, c₁, v) => if c ≤ c₁ then v else ⟨#[lookupScript c], rfl⟩
where
  str : String := include_str "../data/Script_Extensions.txt"
  table : Thunk <| Array (UInt32 × UInt32 × ScriptSet) :=
    parseDataTable str fun _ _ x =>
      let a := x[0]!.split ' ' |>.toArray.map fun s =>
        let s := ofHexString! s
        if h : Script.isValid s then ⟨s, h⟩ else panic! "invalid script code"
      if h : ScriptSet.isSorted a then ⟨a, h⟩ else panic! "unsorted script set"
