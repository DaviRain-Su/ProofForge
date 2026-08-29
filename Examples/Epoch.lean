import ProofForge

namespace Examples.Epoch

open ProofForge.Svm.Sdk

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
  Sysvar.EpochSchedule.slotsPerEpoch

/-- Number of slots before an epoch at which its leader schedule is calculated. -/
@[pf_entry]
def leaderOffset (_s : State) : UInt64 :=
  Sysvar.EpochSchedule.leaderScheduleSlotOffset

/-- Whether epoch warmup is active. -/
@[pf_entry]
def isWarmup (_s : State) : Bool :=
  Sysvar.EpochSchedule.warmup

/-- First epoch after warmup. -/
@[pf_entry]
def normalEpoch (_s : State) : UInt64 :=
  Sysvar.EpochSchedule.firstNormalEpoch

/-- First slot after warmup. -/
@[pf_entry]
def normalSlot (_s : State) : UInt64 :=
  Sysvar.EpochSchedule.firstNormalSlot

/-- 把 slots_per_epoch 写进状态。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := Sysvar.EpochSchedule.slotsPerEpoch },
      Sysvar.EpochSchedule.slotsPerEpoch)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

end Examples.Epoch
