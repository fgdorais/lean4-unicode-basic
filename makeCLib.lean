import UnicodeData

open Unicode

def clibDir : System.FilePath := "."/"UnicodeCLib"

def Unicode.GC.BP : GC := (0x80000000 : UInt32)
def Unicode.GC.LC0 : GC := GC.LC
def Unicode.GC.LC1 : GC := GC.LC ||| GC.BP
def Unicode.GC.PG0 : GC := GC.PG
def Unicode.GC.PG1 : GC := GC.PG ||| GC.BP
def Unicode.GC.PQ0 : GC := GC.PQ
def Unicode.GC.PQ1 : GC := GC.PQ ||| GC.BP

def propTable : Array (UInt32 × UInt32 × UInt64) := Id.run do
  let mut t : Array (UInt32 × UInt32 × UInt64) := #[(0, 0, GC.Cc.toUInt64)]
  for data in UnicodeData.data[1:] do
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
    if data.name.takeRight 7 == ", Last>" then
      t := t.pop.push (c₀, c, d)
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
  for data in UnicodeData.data do
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

def main : IO UInt32 := do
  makeCaseC
  makePropC
  return 0
