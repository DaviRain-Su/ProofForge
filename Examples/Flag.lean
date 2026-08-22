import ProofForge

namespace Examples.Flag

structure State where
  flag : UInt8
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (count : UInt64) : State :=
  { flag := 0, count }

@[pf_entry]
def getFlag (s : State) : UInt64 :=
  s.flag.toUInt64

/-- 把 `bit` 的低 8 位写进 `flag`。 -/
@[pf_entry]
def setFlag (s : State) (bit : UInt64) : Except Error (State × UInt64) :=
  if bit ≤ 255 then
    let next := bit.toUInt8
    .ok ({ flag := next, count := s.count }, next.toUInt64)
  else
    .error .overflow

end Examples.Flag
