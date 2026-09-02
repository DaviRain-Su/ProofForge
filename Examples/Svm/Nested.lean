import ProofForge

/-!
嵌套 structure。抽出器摊成 `book_price` / `book_size` / `baseFree`。
这是可组合性的底座：Lean 侧组合类型，链上仍是扁平 u64 槽。
-/
namespace Examples.Svm.Nested
structure Book where
  price : UInt64
  size : UInt64
  deriving Repr, DecidableEq, Inhabited

structure State where
  book : Book
  baseFree : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (price : UInt64) : State :=
  { book := { price, size := 0 }, baseFree := 0 }

@[pf_entry]
def bestAsk (s : State) : UInt64 :=
  s.book.price

@[pf_entry]
def askSize (s : State) : UInt64 :=
  s.book.size

/-- 改嵌套 `book.size`。 -/
@[pf_entry]
def postAsk (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.book.size ≤ u64Max - size then
    .ok ({ s with book := { s.book with size := s.book.size + size } }, size)
  else
    .error .overflow

end Examples.Svm.Nested