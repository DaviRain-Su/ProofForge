import ProofForge

namespace Examples.Epoch

open ProofForge.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- view：当前 `EpochSchedule.slots_per_epoch`。 -/
@[pf_entry]
def span (_s : State) : UInt64 :=
  slotsPerEpoch

/-- 把 slots_per_epoch 写进状态。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := slotsPerEpoch }, slotsPerEpoch)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

end Examples.Epoch
