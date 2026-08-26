import ProofForge

namespace Examples.RawEntry

open ProofForge.Svm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .rejected

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

/-- A protocol-owned wire entry: `07 || small:u8 || wide:u64`. Physical account 0 must be the
current executable program and account 1 must sign. The method is deliberately independent of the
generated `State`; persistent protocol data belongs in explicit account-storage components. -/
@[pf_entry, pf_svm_raw 7 2 0]
def packed (_s : State) (small : UInt8) (wide : UInt64) : UInt64 :=
  small.toUInt64 + wide + (signerKey 1 &&& 0)

/-- A reusable variable codec probe:
`08 || side:u8 || Option<u64> || Option<u32> || Option<u32>`. Each option lowers to a presence
scalar and a value scalar; absent values are zeroed by the adapter before the method CFG runs. -/
@[pf_entry, pf_svm_raw_borsh_options 8 2 0 1 [8, 4, 4]]
def borshOptions (_s : State) (side tickPresent : UInt8) (tick : UInt64)
    (searchPresent : UInt8) (search : UInt32) (cancelPresent : UInt8)
    (cancel : UInt32) : UInt64 :=
  side.toUInt64 + tickPresent.toUInt64 + tick + 2 * searchPresent.toUInt64 +
    search.toUInt64 + 4 * cancelPresent.toUInt64 + cancel.toUInt64 + (signerKey 1 &&& 0)

end Examples.RawEntry
