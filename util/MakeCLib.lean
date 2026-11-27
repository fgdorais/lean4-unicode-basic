module
import Builders

open Unicode

def clibDir : System.FilePath := ".."/"UnicodeCLib"

def libDir : System.FilePath := ".."/"UnicodeBasic"

def propTable : Array (UInt32 × UInt32 × UInt64) := Id.run do
  let mut t : Array (UInt32 × UInt32 × UInt64) := #[(0, 0, GC.Cc.toUInt64)]
  for data in UnicodeData.data.get[1:] do
    let c := data.code
    let gc := data.gc
    let mut op : UInt64 := 0
    if PropList.isOtherUppercase c then
      op := op ||| 0x100000000
    if PropList.isOtherLowercase c then
      op := op ||| 0x200000000
    if PropList.isOtherAlphabetic c then
      op := op ||| 0x400000000
    if PropList.isOtherMath c then
      op := op ||| 0x800000000
    let d := op ||| gc.toUInt64
    let (c₀, c₁, d₀) := t.back!
    if data.name.takeEnd 7 == ", Last>" then
      t := t.pop.push (c₀, c, d)
      continue
    else if c = c₁ + 1 then
      if d = d₀ then
        t := t.pop.push (c₀, c, d)
        continue
      else if op = d₀ &&& 0xFFFFFFFF00000000 then
        let gc₀ : GC := d₀.toUInt32
        if gc == .Lu then
          if c &&& 1 == 0 then
            if gc₀ == .LC0 || (c₀ == c₁ && gc₀ == .Ll) then
              t := t.pop.push (c₀, c, op ||| GC.LC0.toUInt64)
              continue
          else
            if gc₀ == .LC1 || (c₀ == c₁ && gc₀ == .Ll) then
              t := t.pop.push (c₀, c, op ||| GC.LC1.toUInt64)
              continue
        else if gc == .Ll then
          if c &&& 1 == 0 then
            if gc₀ == .LC1 || (c₀ == c₁ && gc₀ == .Lu) then
              t := t.pop.push (c₀, c, op ||| GC.LC1.toUInt64)
              continue
          else
            if gc₀ == .LC0 || (c₀ == c₁ && gc₀ == .Lu) then
              t := t.pop.push (c₀, c, op ||| GC.LC0.toUInt64)
              continue
        else if gc == .Ps then
          if c &&& 1 == 0 then
            if gc₀ == .PG0 || (c₀ == c₁ && gc₀ == .Pe) then
              t := t.pop.push (c₀, c, op ||| GC.PG0.toUInt64)
              continue
          else
            if gc₀ == .PG1 || (c₀ == c₁ && gc₀ == .Pe) then
              t := t.pop.push (c₀, c, op ||| GC.PG1.toUInt64)
              continue
        else if gc == .Pe then
          if c &&& 1 == 0 then
            if gc₀ == .PG1 || (c₀ == c₁ && gc₀ == .Ps) then
              t := t.pop.push (c₀, c, op ||| GC.PG1.toUInt64)
              continue
          else
            if gc₀ == .PG0 || (c₀ == c₁ && gc₀ == .Ps) then
              t := t.pop.push (c₀, c, op ||| GC.PG0.toUInt64)
              continue
        else if gc == .Pi then
          if c &&& 1 == 0 then
            if gc₀ == .PQ0 || (c₀ == c₁ && gc₀ == .Pf) then
              t := t.pop.push (c₀, c, op ||| GC.PQ0.toUInt64)
              continue
          else
            if gc₀ == .PQ1 || (c₀ == c₁ && gc₀ == .Pf) then
              t := t.pop.push (c₀, c, op ||| GC.PQ1.toUInt64)
              continue
        else if gc == .Pf then
          if c &&& 1 == 0 then
            if gc₀ == .PQ1 || (c₀ == c₁ && gc₀ == .Pi) then
              t := t.pop.push (c₀, c, op ||| GC.PQ1.toUInt64)
              continue
          else
            if gc₀ == .PQ0 || (c₀ == c₁ && gc₀ == .Pi) then
              t := t.pop.push (c₀, c, op ||| GC.PQ0.toUInt64)
              continue
    t := t.push (c, c, d)
  return t

def caseTable : Array (UInt32 × UInt32 × UInt64) := Id.run do
  let mut t := #[]
  for data in UnicodeData.data.get do
    match data with
    | ⟨_, _, _, _, _, _, _, _, none, none, none⟩ => continue
    | ⟨c, _, _, _, _, _, _, _, um, lm, tm⟩ =>
      let uc := match um with | some uc => uc.val | _ => c
      let lc := match lm with | some lc => lc.val | _ => c
      let tc := match tm with | some tc => tc.val | _ => uc
      let v : UInt64 := uc.toUInt64 ||| ((lc.toUInt64 ||| tc.toUInt64 <<< (21 : UInt64))) <<< (21 : UInt64)
      match t.back? with
      | some (c₀,c₁,v₀) =>
        if (c == c₁ + 1) && (v == v₀) then
          t := t.pop.push (c₀, c, v)
        else
          t := t.push (c, c, v)
      | _ =>
          t := t.push (c, c, v)
  return t

def scriptTable : Array (UInt32 × UInt32 × UInt64) :=
  let t := Scripts.data.get.toArray.flatMap fun (sc, t) =>
    let sc := Script.ofAbbrev! <| PropertyValueAliases.getShortName! "sc" sc
    t.map fun (c₀, c₁) => (c₀, c₁, sc.code.toUInt64)
  t.qsort fun (a, _) (b, _) => a < b

/-- Drop the rows of `table` with data `default` and merge adjacent rows with equal data -/
def compressTable (table : Array (UInt32 × UInt32 × UInt64)) (default : UInt64) :
    Array (UInt32 × UInt32 × UInt64) := Id.run do
  let mut t := #[]
  for (c₀, c₁, d) in table do
    if d == default then continue
    match t.back? with
    | some (a, b, e) =>
      if c₀ == b + 1 && d == e then
        t := t.pop.push (a, c₁, d)
      else
        t := t.push (c₀, c₁, d)
    | none => t := t.push (c₀, c₁, d)
  return t

/-- `Bidi_Class` table: constructor index of the class, default `BN` -/
def bidiClassTable : IO (Array (UInt32 × UInt32 × UInt64)) := do
  let t ← mkBidiClass
  return compressTable (t.map fun (c₀, c₁, bc) => (c₀, c₁, bc.ctorIdx.toUInt64))
    BidiClass.boundaryNeutral.ctorIdx.toUInt64

/-- `Canonical_Combining_Class` table: the class, default `0` -/
def combiningClassTable : IO (Array (UInt32 × UInt32 × UInt64)) := do
  let t ← mkCanonicalCombiningClass
  return compressTable (t.map fun (c₀, c₁, cc) => (c₀, c₁, cc.toUInt64)) 0

/-- `Bidi_Mirrored` table: `1` for mirrored, default `0` -/
def bidiMirroredTable : IO (Array (UInt32 × UInt32 × UInt64)) := do
  let t ← mkBidiMirrored
  return compressTable (t.map fun (c₀, c₁) => (c₀, c₁, 1)) 0

/-- `Default_Ignorable_Code_Point` table: `1` for ignorable, default `0` -/
def defaultIgnorableTable : IO (Array (UInt32 × UInt32 × UInt64)) := do
  let t ← mkDefaultIgnorableCodePoint
  return compressTable (t.map fun (c₀, c₁) => (c₀, c₁, 1)) 0

/-- `Numeric_Type` and `Numeric_Value` table, default `0` (no value)

* bits 0-1: `1` for decimal, `2` for digit, `3` for numeric;
* decimal and digit: bits 2-22 hold the first code point of the range, and bits 23-26 the
  value of that code point;
* numeric: bit 2 is the sign, bits 3-11 the denominator (`0` for none), bits 12-51 the absolute
  value of the numerator. -/
def numericTable : IO (Array (UInt32 × UInt32 × UInt64)) := do
  let t ← mkNumericValue
  let t := t.map fun (c₀, c₁, n) =>
    let d : UInt64 := match n with
      | .decimal v => (1 : UInt64) ||| c₀.toUInt64 <<< 2 ||| v.val.toUInt64 <<< 23
      | .digit v => (2 : UInt64) ||| c₀.toUInt64 <<< 2 ||| v.val.toUInt64 <<< 23
      | .numeric n d =>
        let d := d.getD 0
        if d ≥ 0x200 || n.natAbs ≥ 0x10000000000 then
          panic! s!"numeric value too large: {n}/{d}"
        else
          let sign : UInt64 := if n < 0 then 4 else 0
          (3 : UInt64) ||| sign ||| d.toUInt64 <<< 3 ||| n.natAbs.toUInt64 <<< 12
    (c₀, c₁, d)
  return compressTable t 0

/-- Merge adjacent rows of `table` with equal data -/
def mergeRows (table : Array (UInt32 × UInt32 × Nat)) :
    Array (UInt32 × UInt32 × Nat) := Id.run do
  let mut t := #[]
  for (c₀, c₁, d) in table do
    match t.back? with
    | some (a, b, e) =>
      if c₀ == b + 1 && d == e then
        t := t.pop.push (a, c₁, d)
      else
        t := t.push (c₀, c₁, d)
    | none => t := t.push (c₀, c₁, d)
  return t

/-- `Case_Folding` table, default `0` (folds to itself)

* bits 0-21: the simple case folding minus the code point, modulo `2^22`, or `0` for none;
* bits 22-84: the full case folding, 21 bits per code point, ended by `0`, when it has at least two
  code points.

The Stability Policy limits full case foldings to three code points, and the generator fails if
one is longer. -/
def caseFoldingTable : IO (Array (UInt32 × UInt32 × Nat)) := do
  let mut t := #[]
  for (c, s, f) in Unicode.CaseFolding.data.get do
    let sd := match s with
      | some s => (s.toNat + 2 ^ 22 - c.toNat) % 2 ^ 22
      | none => 0
    let f := if 2 ≤ f.size then f.toList else []
    if f.length > 3 then
      throw <| .userError s!"full case folding of {toHexStringRaw c} has more than 3 code points"
    let fd := f.zipIdx.foldl (init := 0) fun n (x, k) => n ||| x.toNat <<< (21 * k)
    let d := sd ||| fd <<< 22
    if d != 0 then
      t := t.push (c, c, d)
  return mergeRows t

/-- `Canonical_Decomposition_Mapping` table, full canonical decompositions of code points other
than Hangul syllables, 21 bits per code point, ended by `0`, default `0` (no decomposition). The
generator fails if a decomposition has more than four code points. -/
def decompositionTable : IO (Array (UInt32 × UInt32 × Nat)) := do
  let mut t := #[]
  for (c, l) in ← mkCanonicalDecompositionMapping do
    if l.length > 4 then
      throw <| .userError
        s!"canonical decomposition of {toHexStringRaw c} has more than 4 code points"
    let d := l.zipIdx.foldl (init := 0) fun n (x, k) => n ||| x.toNat <<< (21 * k)
    t := t.push (c, c, d)
  return mergeRows t

/-- Value of a `prop` row at code point `c`: the `GC` pairs `LC`, `PG` and `PQ`, which alternate
between their two categories, are resolved to the category of `c` -/
def propValue (c : UInt32) (d : Nat) : Nat :=
  let gc := d % 0x40000000
  let pb := (d >>> 31) % 2
  let op := d - d % 0x100000000
  let pick (a b : Nat) : Nat := if c.toNat % 2 == pb then a else b
  if gc == GC.LC.toUInt64.toNat then op ||| pick GC.Lu.toUInt64.toNat GC.Ll.toUInt64.toNat
  else if gc == GC.PG.toUInt64.toNat then op ||| pick GC.Ps.toUInt64.toNat GC.Pe.toUInt64.toNat
  else if gc == GC.PQ.toUInt64.toNat then op ||| pick GC.Pi.toUInt64.toNat GC.Pf.toUInt64.toNat
  else op ||| gc

/-- Values of `table` at every code point, `default` outside its rows; `value c d` is the value
at `c` in a row with data `d` -/
def expand (table : Array (UInt32 × UInt32 × Nat)) (default : Nat)
    (value : UInt32 → Nat → Nat := fun _ d => d) : Array Nat := Id.run do
  let mut v := Array.replicate 0x110000 default
  for (c₀, c₁, d) in table do
    for c in [c₀.toNat:c₁.toNat+1] do
      v := v.set! c (value c.toUInt32 d)
  return v

/-- Smallest C unsigned type that holds `0` to `n - 1` -/
def indexType (n : Nat) : String := if n ≤ 0x100 then "uint8_t" else "uint16_t"

/-- Write `UnicodeCLib/<file>.c` with the three-stage table of `values` (one per code point) and
the C function `unicode_<file>_lookup`. Stage 1 gives the number of the 256-code-point block of
each code point, stage 2 the index in `value` of each code point of each distinct block, and
`value` the distinct values. With `wide`, values have 128 bits and the C functions
`unicode_<file>_lookup_lo` and `unicode_<file>_lookup_hi` return their low and high 64 bits;
otherwise `unicode_<file>_lookup` returns them as `type`. -/
def makeStageC (file type : String) (values : Array Nat) (default : Nat) (wide := false) :
    IO Unit := do
  let distinct : Array Nat := Id.run do
    let mut seen : Std.HashMap Nat Unit := {}
    for v in values do seen := seen.insert v ()
    return seen.keys.toArray.qsort (· < ·)
  let index : Std.HashMap Nat Nat := distinct.foldl (init := {}) fun m v => m.insert v m.size
  let mut blocks : Std.HashMap (Array Nat) Nat := {}
  let mut stage1 : Array Nat := #[]
  let mut stage2 : Array (Array Nat) := #[]
  for b in [0:0x1100] do
    let block := (values.extract (b * 256) (b * 256 + 256)).map (index[·]!)
    match blocks[block]? with
    | some n => stage1 := stage1.push n
    | none =>
      blocks := blocks.insert block stage2.size
      stage1 := stage1.push stage2.size
      stage2 := stage2.push block
  if stage2.size > 0x10000 || distinct.size > 0x10000 then
    throw <| .userError s!"{file}: too many blocks or values"
  let lit (v : Nat) : String :=
    if wide then s!"\{UINT64_C({v % 2 ^ 64}),UINT64_C({v / 2 ^ 64})}"
    else if type == "uint32_t" then s!"UINT32_C({v})" else s!"UINT64_C({v})"
  let valueDecl := if wide then s!"static const uint64_t value[{distinct.size}][2];"
    else s!"static const {type} value[{distinct.size}];"
  let lookup (name index : String) : String := s!"{if wide then "uint64_t" else type} unicode_{file}_{name}(uint32_t c) \{
  if (c > 0x10FFFF) return {if wide then "0" else lit default};
  return value[stage2[stage1[c >> 8]][c & 0xFF]]{index};
}"
  let body := if wide then lookup "lookup_lo" "[0]" ++ "\n\n" ++ lookup "lookup_hi" "[1]"
    else lookup "lookup" ""
  IO.FS.withFile (clibDir / s!"{file}.c") .write fun h => do
    h.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

static const {indexType stage2.size} stage1[0x1100];
static const {indexType distinct.size} stage2[{stage2.size}][256];
{valueDecl}

{body}

static const {indexType stage2.size} stage1[] = \{"
    for i in [0:stage1.size:32] do
      h.putStrLn <| ",".intercalate (stage1.extract i (i + 32) |>.toList.map toString) ++ ","
    h.putStrLn ("};

static const " ++ indexType distinct.size ++ " stage2[][256] = {")
    for block in stage2 do
      h.putStrLn <| "{" ++ ",".intercalate (block.toList.map toString) ++ "},"
    h.putStrLn s!"};

static const {if wide then "uint64_t" else type} value[]{if wide then "[2]" else ""} = \{"
    for v in distinct do
      h.putStrLn s!"{lit v},"
    h.putStrLn "};"

/-- Maximum number of ranges in a leaf of the `Internal.BTree` copies of the C tables -/
def leafSize : Nat := 64

/-- `n` as a Lean raw hexadecimal literal -/
def natLit (n : Nat) : String :=
  "(nat_lit 0x" ++ (String.ofList (Nat.toDigits 16 n)).toUpper ++ ")"

/-- B-tree on entries `lo` to `hi - 1` of `table`, as Lean source, bisecting the rows; the
values of a leaf are packed `width` bits each -/
def btree (table : Array (UInt32 × UInt32 × Nat)) (width : Nat) (indent : String)
    (lo hi : Nat) : String :=
  let indent' := indent ++ "  "
  if hi - lo ≤ leafSize then
    let rows := table[lo:hi].toArray.zipIdx
    let keys := rows.foldl (init := 0) fun n ((c₀, c₁, _), k) =>
      n ||| (c₀.toNat ||| c₁.toNat <<< 21) <<< (42 * k)
    let block := rows.foldl (init := 0) fun n ((_, _, d), k) => n ||| d <<< (width * k)
    s!".leaf {lo} {hi}\n{indent'}{natLit keys}\n{indent'}{natLit block}"
  else
    let mid := (lo + hi) / 2
    s!".node {natLit table[mid]!.1.toNat}\n{indent'}({btree table width indent' lo mid})"
      ++ s!"\n{indent'}({btree table width indent' mid hi})"
termination_by hi - lo
decreasing_by all_goals simp only [leafSize] at *; lia

/-- `table` with its data as `Nat` -/
def natData (table : Array (UInt32 × UInt32 × UInt64)) : Array (UInt32 × UInt32 × Nat) :=
  table.map fun (c₀, c₁, d) => (c₀, c₁, d.toNat)

/-- `n` bits, in words -/
def bits (n : Nat) : String := if n == 1 then "1 bit" else s!"{n} bits"

/-- Write `UnicodeBasic/Internal/<module>.lean` with `table` as the B-tree `Internal.<name>` -/
def makeTreeLean (module name c : String) (table : Array (UInt32 × UInt32 × Nat))
    (width : Nat) : IO Unit :=
  IO.FS.withFile (libDir / "Internal" / s!"{module}.lean") .write fun file => do
    file.putStrLn s!"/- THIS IS A GENERATED FILE - DO NOT EDIT -/
module
public import UnicodeBasic.Internal.BTree

/-! # Kernel copy of the `{c}` table

This module holds the same data as `UnicodeCLib/{c}.c` as a B-tree, for the kernel
to read. It is internal and may change at any time.
-/

namespace Unicode.Internal

-- The block of each leaf holds the `{c}.c` data of its ranges, {bits width} each.
--
-- This must stay `noncomputable`: compiled code uses the C table, and a computable definition
-- would build this tree when a program starts.
/-- The `{c}` table (internal use only) -/
@[expose] public noncomputable def {name} : BTree Nat :=
  {btree table width "  " 0 table.size}"

public def main : IO UInt32 := do
  makeStageC "case" "uint64_t" (expand (natData caseTable) 0) 0
  makeTreeLean "CaseTree" "caseTree" "case" (natData caseTable) 63
  makeStageC "prop" "uint64_t" (expand (natData propTable) GC.Cn.toUInt64.toNat propValue)
    GC.Cn.toUInt64.toNat
  makeTreeLean "PropTree" "propTree" "prop" (natData propTable) 36
  let unknown := (Script.ofAbbrev! "Zzzz").code.toNat
  makeStageC "script" "uint32_t" (expand (natData scriptTable) unknown) unknown
  makeTreeLean "ScriptTree" "scriptTree" "script" (natData scriptTable) 32
  for (module, name, file, table, default, width) in [
      ("BidiClassTree", "bidiClassTree", "bidi_class", ← bidiClassTable,
        BidiClass.boundaryNeutral.ctorIdx.toUInt64, 5),
      ("BidiMirroredTree", "bidiMirroredTree", "bidi_mirrored", ← bidiMirroredTable, 0, 1),
      ("CombiningClassTree", "combiningClassTree", "combining_class",
        ← combiningClassTable, 0, 8),
      ("DefaultIgnorableTree", "defaultIgnorableTree", "default_ignorable",
        ← defaultIgnorableTable, 0, 1),
      ("NumericTree", "numericTree", "numeric", ← numericTable, 0, 52)] do
    makeStageC file "uint64_t" (expand (natData table) default.toNat) default.toNat
    makeTreeLean module name file (natData table) width
  for (module, name, file, table, width) in [
      ("CaseFoldingTree", "caseFoldingTree", "case_folding", ← caseFoldingTable, 85),
      ("DecompositionTree", "decompositionTree", "decomposition", ← decompositionTable, 84)] do
    makeStageC file "" (expand table 0) 0 (wide := true)
    makeTreeLean module name file table width
  return 0
