import SolanaLean

namespace Examples.Epoch

open SolanaLean.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- view：当前 `EpochSchedule.slots_per_epoch`。 -/
@[solana_entry]
def span (_s : State) : UInt64 :=
  slotsPerEpoch

/-- 把 slots_per_epoch 写进状态。 -/
@[solana_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := slotsPerEpoch }, slotsPerEpoch)
  else
    .error .overflow

@[solana_entry]
def get (s : State) : UInt64 :=
  s.dummy

end Examples.Epoch
