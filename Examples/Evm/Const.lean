import ProofForge

namespace Examples.Evm.Const
open ProofForge.Evm.Runtime

/-- dummy 占槽；seed / who 走构造期 immutable，不进 storage。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- ctor 参数 `seed`/`salt`/`who`/`peer` 烘焙进 bytecode。dummy 仍是 0。 -/
@[pf_entry]
def init (_seed _salt : UInt64) (_who _peer : Addr20) : State :=
  { dummy := 0 }

/-- 写 dummy。immutable 不受影响。 -/
@[pf_entry]
def touch (_s : State) (v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := v }, v)
  else
    .error .overflow

/-- 构造期 `uint64`。不是 `sload`。 -/
@[pf_entry]
def seedOf (_s : State) : UInt64 :=
  evmImmU64

/-- 第二套构造期 `uint64`。 -/
@[pf_entry]
def saltOf (_s : State) : UInt64 :=
  evmImmU64b

/-- 构造期 Addr20。不是 storage owner。 -/
@[pf_entry]
def whoOf (_s : State) : Addr20 :=
  evmImm20

/-- 第二套构造期 Addr20。 -/
@[pf_entry]
def peerOf (_s : State) : Addr20 :=
  evmImm20b

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

end Examples.Evm.Const