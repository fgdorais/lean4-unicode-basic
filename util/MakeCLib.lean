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

def makePropC : IO Unit :=
  IO.FS.withFile (clibDir / "prop.c") .write fun file => do
    file.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

#define TABLE_SIZE {propTable.size}"
    file.putStrLn "
static const unicode_data_t table[TABLE_SIZE];

uint64_t unicode_prop_lookup(uint32_t c) {
  unicode_data_t v;
  if (c >= table[0].cmin) {
    unsigned int lo = 0;
    unsigned int hi = TABLE_SIZE;
    unsigned int i = (lo + hi)/2;
    while (i != lo) {
      if (c < table[i].cmin) hi = i;
      else lo = i;
      i = (lo + hi)/2;
    }
    v = table[i];
    if (c <= v.cmax) {
      uint32_t gc = v.data & UNICODE_GC;
      uint32_t pb = (v.data >> 31) & 1;
      uint64_t op = v.data & UINT64_C(0xffffffff00000000);
      if (gc == UNICODE_GC_LC) {
        if ((c & 1) == pb) return op | UNICODE_GC_Lu;
        else return op | UNICODE_GC_Ll;
      }
      if (gc == UNICODE_GC_PG) {
        if ((c & 1) == pb) return op | UNICODE_GC_Ps;
        else return op | UNICODE_GC_Pe;
      }
      if (gc == UNICODE_GC_PQ) {
        if ((c & 1) == pb) return op | UNICODE_GC_Pi;
        else return op | UNICODE_GC_Pf;
      }
      return op | gc;
    }
  }
  return UNICODE_GC_Cn;
}

static const unicode_data_t table[] = {"
    for (c₀, c₁, d) in propTable do
      file.putStrLn s!"\{UINT32_C({c₀}),UINT32_C({c₁}),UINT64_C({d})},"
    file.putStrLn "};"

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

def makeCaseC : IO Unit :=
  IO.FS.withFile (clibDir / "case.c") .write fun file => do
    file.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

#define TABLE_SIZE {caseTable.size}"
    file.putStrLn "
static const unicode_data_t table[TABLE_SIZE];

uint64_t unicode_case_lookup(uint32_t c) {
  unicode_data_t v;
  if (c >= table[0].cmin) {
    unsigned int lo = 0;
    unsigned int hi = TABLE_SIZE;
    unsigned int i = (lo + hi)/2;
    while (i != lo) {
      if (c < table[i].cmin) hi = i;
      else lo = i;
      i = (lo + hi)/2;
    }
    if (c <= table[i].cmax) return table[i].data;
  }
  return 0;
}

static const unicode_data_t table[] = {"
    for (c₀, c₁, d) in caseTable do
      file.putStrLn s!"\{UINT32_C({c₀}),UINT32_C({c₁}),UINT64_C({d})},"
    file.putStrLn "};"

def scriptTable : Array (UInt32 × UInt32 × UInt64) :=
  let t := Scripts.data.get.toArray.flatMap fun (sc, t) =>
    let sc := Script.ofAbbrev! <| PropertyValueAliases.getShortName! "sc" sc
    t.map fun (c₀, c₁) => (c₀, c₁, sc.code.toUInt64)
  t.qsort fun (a, _) (b, _) => a < b

def makeScriptC : IO Unit :=
  IO.FS.withFile (clibDir / "script.c") .write fun file => do
    file.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

#define TABLE_SIZE {scriptTable.size}
#define SCRIPT_UNKNOWN UINT32_C({Script.ofAbbrev! "Zzzz" |>.code})"
    file.putStrLn "
static const unicode_data_t table[TABLE_SIZE];

uint32_t unicode_script_lookup(uint32_t c) {
  unicode_data_t v;
  if (c >= table[0].cmin) {
    unsigned int lo = 0;
    unsigned int hi = TABLE_SIZE;
    unsigned int i = (lo + hi)/2;
    while (i != lo) {
      if (c < table[i].cmin) hi = i;
      else lo = i;
      i = (lo + hi)/2;
    }
    if (c <= table[i].cmax) return (uint32_t)table[i].data;
  }
  return SCRIPT_UNKNOWN;
}

static const unicode_data_t table[] = {"
    for (c₀, c₁, d) in scriptTable do
      file.putStrLn s!"\{UINT32_C({c₀}),UINT32_C({c₁}),UINT64_C({d})},"
    file.putStrLn "};"

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

/-- Write `UnicodeCLib/<file>.c` with `table` and the C function `unicode_<file>_lookup`, which
returns the data of the range containing a code point, or `default` -/
def makeTableC (file : String) (table : Array (UInt32 × UInt32 × UInt64)) (default : UInt64) :
    IO Unit :=
  IO.FS.withFile (clibDir / s!"{file}.c") .write fun h => do
    h.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

#define TABLE_SIZE {table.size}
#define DEFAULT UINT64_C({default})

static const unicode_data_t table[TABLE_SIZE];

uint64_t unicode_{file}_lookup(uint32_t c) \{
  if (c >= table[0].cmin) \{
    unsigned int lo = 0;
    unsigned int hi = TABLE_SIZE;
    unsigned int i = (lo + hi)/2;
    while (i != lo) \{
      if (c < table[i].cmin) hi = i;
      else lo = i;
      i = (lo + hi)/2;
    }
    if (c <= table[i].cmax) return table[i].data;
  }
  return DEFAULT;
}

static const unicode_data_t table[] = \{"
    for (c₀, c₁, d) in table do
      h.putStrLn s!"\{UINT32_C({c₀}),UINT32_C({c₁}),UINT64_C({d})},"
    h.putStrLn "};"

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

/-- Write `UnicodeCLib/<file>.c` with `table`, whose data has at most 128 bits, and the C
function `unicode_<file>_lookup`, which returns the data of the range containing a code point, or
`0`, as a `CLib.Row` -/
def makeWideTableC (file : String) (table : Array (UInt32 × UInt32 × Nat)) : IO Unit :=
  IO.FS.withFile (clibDir / s!"{file}.c") .write fun h => do
    h.putStrLn s!"/* THIS IS A GENERATED FILE - DO NOT EDIT */
#include \"basic.h\"

#define TABLE_SIZE {table.size}

static const unicode_wide_data_t table[TABLE_SIZE];

lean_obj_res unicode_{file}_lookup(uint32_t c) \{
  uint64_t lo = 0, hi = 0;
  if (c >= table[0].cmin) \{
    unsigned int l = 0;
    unsigned int h = TABLE_SIZE;
    unsigned int i = (l + h)/2;
    while (i != l) \{
      if (c < table[i].cmin) h = i;
      else l = i;
      i = (l + h)/2;
    }
    if (c <= table[i].cmax) \{
      lo = table[i].lo;
      hi = table[i].hi;
    }
  }
  return unicode_row(lo, hi);
}

static const unicode_wide_data_t table[] = \{"
    for (c₀, c₁, d) in table do
      if d ≥ 2 ^ 128 then throw <| .userError s!"{file}: data too wide at {toHexStringRaw c₀}"
      h.putStrLn
        s!"\{UINT32_C({c₀}),UINT32_C({c₁}),UINT64_C({d % 2 ^ 64}),UINT64_C({d / 2 ^ 64})},"
    h.putStrLn "};"

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

/-- Maximum number of ranges in a leaf of the `Internal.BTree` copies of the C tables -/
def leafSize : Nat := 64

/-- `n` as a Lean raw hexadecimal literal -/
def natLit (n : Nat) : String :=
  "(nat_lit 0x" ++ (String.ofList (Nat.toDigits 16 n)).toUpper ++ ")"

/-- B-tree on entries `lo` to `hi - 1` of `table`, as Lean source, following the C search; the
values of a leaf are packed `width` bits each -/
partial def btree (table : Array (UInt32 × UInt32 × Nat)) (width : Nat) (indent : String)
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

This module holds the same table as `UnicodeCLib/{c}.c` as a B-tree, for the kernel
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
  makeCaseC
  makeTreeLean "CaseTree" "caseTree" "case" (natData caseTable) 63
  makePropC
  makeTreeLean "PropTree" "propTree" "prop" (natData propTable) 36
  makeScriptC
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
    makeTableC file table default
    makeTreeLean module name file (natData table) width
  for (module, name, file, table, width) in [
      ("CaseFoldingTree", "caseFoldingTree", "case_folding", ← caseFoldingTable, 85),
      ("DecompositionTree", "decompositionTree", "decomposition", ← decompositionTable, 84)] do
    makeWideTableC file table
    makeTreeLean module name file table width
  return 0
