import ProofForge

namespace Examples.Keys

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

/-- 无参 mutate 占入口。 -/
@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

@[pf_entry]
def key00 (_s : State) : UInt64 :=
  accKeyWord 0 0

@[pf_entry]
def key01 (_s : State) : UInt64 :=
  accKeyWord 0 1

@[pf_entry]
def key02 (_s : State) : UInt64 :=
  accKeyWord 0 2

@[pf_entry]
def key03 (_s : State) : UInt64 :=
  accKeyWord 0 3

@[pf_entry]
def owner00 (_s : State) : UInt64 :=
  accOwnerWord 0 0

@[pf_entry]
def owner03 (_s : State) : UInt64 :=
  accOwnerWord 0 3

@[pf_entry]
def key10 (_s : State) : UInt64 :=
  accKeyWord 1 0

@[pf_entry]
def key13 (_s : State) : UInt64 :=
  accKeyWord 1 3

@[pf_entry]
def owner10 (_s : State) : UInt64 :=
  accOwnerWord 1 0

@[pf_entry]
def owner13 (_s : State) : UInt64 :=
  accOwnerWord 1 3

end Examples.Keys
