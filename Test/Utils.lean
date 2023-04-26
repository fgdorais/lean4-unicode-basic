
structure Bubble (α) [Ord α] extends Array α
deriving Inhabited

namespace Bubble
variable {α} [Ord α] (bs : Bubble α)

abbrev size := bs.toArray.size

abbrev isEmpty := bs.toArray.isEmpty

abbrev empty : Bubble α where
  toArray := #[]

abbrev push (val : α) : Bubble α where
  toArray := bs.toArray.push val

abbrev pushArray (vals : Array α) : Bubble α where
  toArray := bs.toArray.append vals

@[inline]
partial def bubble (rel : α → α → Bool) : Array α :=
  let rec loop (as : Array α) (val : α) (i : Nat) (h : i < as.size) : Array α :=
    if _ : i + 1 < as.size then
      if rel as[i + 1] val then
        loop (as.set ⟨i, h⟩ as[i+1]) val (i+1) (by rw [Array.size_set]; assumption)
      else
        loop (as.set ⟨i, h⟩ val) as[i + 1] (i+1) (by rw [Array.size_set]; assumption)
    else
      as.set ⟨i, h⟩ val
  if h : bs.size > 0 then
    loop bs.toArray bs.toArray[0] 0 h
  else
    bs.toArray

def popMax? : Option (α × Bubble α) := do
  let as := bubble bs fun x y => compare x y == .lt
  let val ← as.back?
  return (val, {toArray:=as.pop})

def popMin? : Option (α × Bubble α) := do
  let as := bubble bs fun x y => compare x y == .gt
  let val ← as.back?
  return (val, {toArray:=as.pop})

end Bubble

local instance (α β) [Ord α] :  Ord (α × β) where
  compare | (x,_), (y,_) => compare x y

structure MergeStream (α) [Ord α] (σ) [Stream σ α] extends Bubble (α × σ)

instance (α) [Ord α] (σ) [Stream σ α] : Stream (MergeStream α σ) α where
  next? s := do
    let ((val, str), bs) ← s.toBubble.popMin?
    match Stream.next? str with
    | some next => return (val, {toBubble := bs.push next})
    | none => return (val, {toBubble := bs})

@[inline]
def MergeStream.mkOfList (α) [Ord α] {σ} [Stream σ α] : List σ → MergeStream α σ :=
  let rec loop : MergeStream α σ → List σ → MergeStream α σ
  | ms, [] => ms
  | ms, s :: ss =>
    match Stream.next? s with
    | some next => loop {toBubble := ms.push next} ss
    | none => loop ms ss
  loop {toBubble := Bubble.empty}

def Stream.toArray {α σ} [Stream σ α] (str : σ) : Array α := Id.run do
  let mut arr := #[]
  for x in str do
    arr := arr.push x
  return arr
