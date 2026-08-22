import SolanaLean

namespace Examples.Lang

structure State where
  cells : Vector UInt64 4
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  | oob
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[solana_entry]
def init (first : UInt64) : State :=
  { cells := #v[first, 0, 0, 0] }

@[solana_entry]
def band (_s : State) (a b : UInt64) : UInt64 :=
  a &&& b

@[solana_entry]
def bor (_s : State) (a b : UInt64) : UInt64 :=
  a ||| b

@[solana_entry]
def bxor (_s : State) (a b : UInt64) : UInt64 :=
  a ^^^ b

@[solana_entry]
def bnot (_s : State) (a : UInt64) : UInt64 :=
  ~~~a

@[solana_entry]
def shl (_s : State) (a n : UInt64) : UInt64 :=
  a <<< n

@[solana_entry]
def shr (_s : State) (a n : UInt64) : UInt64 :=
  a >>> n

/-- 有界 `for i in [0:4]` 累加四格。 -/
@[solana_entry]
def sum4 (s : State) : UInt64 :=
  Id.run do
    let mut acc : UInt64 := 0
    for i in [0:4] do
      acc := acc + s.cells[i]!
    return acc

/-- 运行时下标读。`i ≥ 4` revert。 -/
@[solana_entry]
def getAt (s : State) (i : UInt64) : UInt64 :=
  if i < 4 then s.cells[i.toNat]! else 0

/-- 运行时下标写。`i ≥ 4` → `oob`。 -/
@[solana_entry]
def setAt (s : State) (i v : UInt64) : Except Error (State × UInt64) :=
  if h : i.toNat < 4 then
    .ok ({ cells := s.cells.set i.toNat v }, v)
  else
    .error .oob

/-- 真 ABI：`uint8` 参数。 -/
@[solana_entry]
def mask8 (_s : State) (b : UInt8) : UInt64 :=
  b.toUInt64

/-- 两叶 return。 -/
@[solana_entry]
def both (s : State) : UInt64 × UInt64 :=
  (s.cells[0]!, s.cells[1]!)

@[solana_entry]
def get (s : State) : UInt64 :=
  s.cells[0]!

end Examples.Lang
