import ProofForge

/-!
固定 4 档 u64 向量。用来钉 SVM 的 `indexGet` / `indexSet` / `forAccum`，
不带位运算，所以整程序能进 sbpf。
-/
namespace Examples.Book

structure State where
  cells : Vector UInt64 4
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (first : UInt64) : State :=
  { cells := #v[first, 0, 0, 0] }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.cells[0]!

@[pf_entry]
def getAt (s : State) (i : UInt64) : UInt64 :=
  if i < 4 then s.cells[i.toNat]! else 0

@[pf_entry]
def setAt (s : State) (i v : UInt64) : Except Error (State × UInt64) :=
  if h : i.toNat < 4 then
    .ok ({ cells := s.cells.set i.toNat v }, v)
  else
    .error .overflow

/-- 有界累加四格。 -/
@[pf_entry]
def sum4 (s : State) : UInt64 :=
  Id.run do
    let mut acc : UInt64 := 0
    for i in [0:4] do
      acc := acc + s.cells[i]!
    return acc

end Examples.Book
