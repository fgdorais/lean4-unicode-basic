/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Hangul
import UnicodeBasic.Types

namespace Unicode

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
private def parseTable (s : String) (f : UInt32 → Array Substring → α) : Thunk <| Array (UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let val := f start record[1:]
    r := r.push (start, val)
  return r

/-- Parse a range compressed data table -/
private def parseDataTable (s : String) (f : UInt32 → UInt32 → Array Substring → α) : Thunk <| Array (UInt32 × UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    let val := f start stop record[2:]
    r := r.push (start, stop, val)
  return r

/-- Parse a range compressed property table -/
private def parsePropTable (s : String) : Thunk <| Array (UInt32 × UInt32) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    r := r.push (start, stop)
  return r

/-- Get bidirectional class using lookup table

  Unicode property: `Bidi_Class` -/
def lookupBidiClass (c : UInt32) : BidiClass :=
  let table := table.get
  if c < table[0]!.1 then .BN else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, bc) => if c ≤ v then bc else .BN
where
  str : String := include_str "../data/table/Bidi_Class.txt"
  table : Thunk <| Array (UInt32 × UInt32 × BidiClass) :=
    parseDataTable str fun _ _ x => BidiClass.ofAbbrev! x[0]!

/-- Get canonical combining class using lookup table

  Unicode property: `Canonical_Combining_Class` -/
def lookupCanonicalCombiningClass (c : UInt32) : Nat :=
  let t := table.get
  if c < t[0]!.1 then 0 else
    match t[find c (fun i => t[i]!.1) 0 t.size.toUSize]! with
    | (_, v, n) => if c ≤ v then n else 0
where
  str : String := include_str "../data/table/Canonical_Combining_Class.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Nat) :=
    parseDataTable str fun _ _ x => x[0]!.toNat?.get!

/-- Get canonical decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
def lookupCanonicalDecompositionMapping (c : UInt32) : List UInt32 :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => [s.getLChar.val, s.getVChar.val, t.val]
    | none => [s.getLChar.val, s.getVChar.val]
  else
    let table := table.get
    if c < table[0]!.1 then [c] else
      match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
      | (v, l) => if c == v then l else [c]
where
  str : String := include_str "../data/table/Canonical_Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × List UInt32) :=
    parseTable str fun _ x => (x.map ofHexString!).toList

/-- Get simple case mappings of a code point using lookup table

  Unicode properties:
    `Simple_Lowercase_Mapping`
    `Simple_Uppercase_Mapping`
    `Simple_Titlecase_Mapping` -/
def lookupCaseMapping (c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let table := table.get
  if c < table[0]!.1 then (c, c, c) else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, mu, ml, mt) => if c ≤ v then (mu.getD c, ml.getD c, mt.getD (mu.getD c)) else (c, c, c)
where
  str : String := include_str "../data/table/Case_Mapping.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Option UInt32 × Option UInt32 × Option UInt32) :=
    parseDataTable str fun _ _ a =>
      match a with
      | #[mu, ml, mt] =>
        let mu := if mu.isEmpty then none else some <| ofHexString! mu
        let ml := if ml.isEmpty then none else some <| ofHexString! ml
        let mt := if mt.isEmpty then none else some <| ofHexString! mt
        (mu, ml, mt)
      | _ => panic! "invalid table data"

/-- Get decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type` -/
def lookupDecompositionMapping? (c : UInt32) : Option DecompositionMapping :=
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
      | (v, t, l) =>
        if c == v then
          some <| .mk t (l.map fun c => Char.ofNat c.toNat).toList
        else
          none
where
  str : String := include_str "../data/table/Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × Option CompatibilityTag × Array UInt32) :=
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
        else panic! s!"invalid compatibility tag {x[0]!}"
      (tag, x[1:].toArray.map ofHexString!)

/-- Get general category of a code point using lookup table

  Unicode property: `General_Category` -/
def lookupGC (c : UInt32) : GC :=
  let table := table.get
  if c < table[0]!.1 then .Cn else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, gc) =>
      if c ≤ v then
        if gc == .LC then
          if c &&& 1 == 0 then .Lu else .Ll
        else if gc == .PG then
          if c &&& 1 == 0 then .Ps else .Pe
        else if gc == .PQ then
          if c &&& 1 == 0 then .Pi else .Pf
        else gc
      else .Cn
where
  str : String := include_str "../data/table/General_Category.txt"
  table : Thunk <| Array (UInt32 × UInt32 × GC) :=
    parseDataTable str fun _ _ x => GC.ofAbbrev! x[0]!

set_option linter.deprecated false in
@[deprecated Unicode.lookupGC (since := "v1.3.0")]
def lookupGeneralCategory (c : UInt32) : GeneralCategory :=
  .ofGC! (lookupGC c)

/-- Get name of a code point using lookup table

  Unicode property: `Name` -/
def lookupName (c : UInt32) : String :=
  let table := table.get
  if c < table[0]!.1 then unreachable! else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, d) =>
      if c ≤ v then
        if d.get 0 == '<' then
          if d == "<Control>" then
            s!"<control-{toHexStringAux c}>"
          else if d == "<Private Use>" then
            s!"<private-use-{toHexStringAux c}>"
          else if d == "<Reserved>" then
            s!"<reserved-{toHexStringAux c}>"
          else if d == "<Surrogate>" then
            s!"<surrogate-{toHexStringAux c}>"
          else if d == "<CJK Unified Ideograph>" then
            "CJK UNIFIED IDEOGRAPH-" ++ toHexStringAux c
          else if d == "<CJK Compatibility Ideograph>" then
            "CJK COMPATIBILITY IDEOGRAPH-" ++ toHexStringAux c
          else if d == "<Hangul Syllable>" then
            "HANGUL SYLLABLE " ++ (Hangul.getSyllable! c).getShortName
          else if d == "<Khitan Small Script Character>" then
            "KHITAN SMALL SCRIPT CHARACTER-" ++ toHexStringAux c
          else if d == "<Nushu Character>" then
            "NUSHU CHARACTER-" ++ toHexStringAux c
          else if d == "<Tangut Component>" then
            let i := toString <| c.toNat - 0x18800 + 1
            let i :=
              if i.length == 1 then "00" ++ i
              else if i.length == 2 then "0" ++ i
              else i
            "TANGUT COMPONENT-" ++ i
          else if d == "<Tangut Ideograph>" then
            "TANGUT IDEOGRAPH-" ++ toHexStringAux c
          else panic! s!"unknown name range {d}"
        else d.toString
      else s!"<noncharacter-{toHexStringAux c}>"
where
  str : String := include_str "../data/table/Name.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Substring) :=
    parseDataTable str fun _ _ x => x[0]!

/-- Get numeric value of a code point using lookup table

  Unicode properties:
    `Numeric_Type`
    `Numeric_Value` -/
def lookupNumericValue (c : UInt32) : Option NumericType :=
  let table := table.get
  if c < table[0]!.1 then none else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (c₀, _, .decimal _) =>
      let val := c.toNat - c₀.toNat
      if h : val < 10 then
        some <| NumericType.decimal ⟨val, h⟩
      else
        none
    | (c₀, c₁, .digit i) =>
      if c ≤ c₁ then
        let val := c.toNat - c₀.toNat + i.val
        if h : val < 10 then
          some <| NumericType.digit ⟨val, h⟩
        else
          panic! "invalid `Numeric_Value` table"
      else
        none
    | ⟨v, _, n⟩ =>
      if c == v then some n else none
where
  str : String := include_str "../data/table/Numeric_Value.txt"
  table : Thunk <| Array (UInt32 × UInt32 × NumericType) :=
    parseDataTable str fun _ _ a =>
      let s := a[0]!.toString
      if s == "decimal" then
        .decimal 0
      else if "digit".isPrefixOf s then
        let d := (s.get ⟨6⟩).toNat
        if h : d - '0'.toNat < 10 then
          if d < '0'.toNat then
            panic! s!"invalid table data {d} {s}"
          else
            .digit ⟨d - '0'.toNat, h⟩
        else
          panic! s!"invalid table data {d} {s}"
      else if "numeric".isPrefixOf s then
        let s := s.drop 8
        match String.splitOn s "/" with
        | [n] => .numeric n.toInt! none
        | [n, d] => .numeric n.toInt! (some d.toNat!)
        | _ => panic! "invalid table data"
      else .numeric (-4) none

/-! Properties -/

/-- Check if code point is alphabetic using lookup table

  Unicode property: `Alphabetic` -/
def lookupAlphabetic (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Alphabetic.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is bidi mirrored using lookup table

  Unicode property: `Bidi_Mirrored`
-/
def lookupBidiMirrored (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Bidi_Mirrored.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a cased letter using lookup table

  Unicode property: `Cased` -/
def lookupCased (c : UInt32 ) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Cased.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a lowercase letter using lookup table

  Unicode property: `Lowercase` -/
def lookupLowercase (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Lowercase.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a mathematical symbol using lookup table

  Unicode property: `Math` -/
def lookupMath (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Math.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a titlecase letter using lookup table

  Unicode property: `Titlecase` -/
def lookupTitlecase (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Titlecase.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a uppercase letter using lookup table

  Unicode property: `Uppercase` -/
def lookupUppercase (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/Uppercase.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

/-- Check if code point is a white space character using lookup table

  Unicode property: `White_Space` -/
def lookupWhiteSpace (c : UInt32) : Bool :=
  let table := table.get
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v
where
  str : String := include_str "../data/table/White_Space.txt"
  table : Thunk <| Array (UInt32 × UInt32) := parsePropTable str

end Unicode
