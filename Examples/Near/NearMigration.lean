import ProofForge

namespace Examples.Near.NearMigration
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  total : UInt64
  revision : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Exact split-storage key owned by the prior one-field Counter schema. -/
@[pf_inline] def legacyValueKey : BoundedBytes 5 :=
  { length := 5, values := #v[118, 97, 108, 117, 101] }

@[pf_entry]
def init (initial : UInt64) : State :=
  { total := initial, revision := 2 }

@[pf_entry]
def increment (state : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if state.total ≤ ~~~(0 : UInt64) - delta then
    let next := state.total + delta
    .ok ({ state with total := next }, next)
  else
    .error .overflow

@[pf_entry]
def get (state : State) : UInt64 :=
  state.total

@[pf_entry]
def revisionOf (state : State) : UInt64 :=
  state.revision

/-- Explicitly authenticated migration from the canonical one-field Counter schema. The current
`State` argument is intentionally ignored: old data is decoded only from its exact prior key. -/
@[pf_entry, pf_near_private, pf_near_migrate 0x8de0fef1e13b14ad]
def migrate (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.read legacyValueKey
  let value := (result.byte 0).toUInt64 |||
    ((result.byte 1).toUInt64 <<< 8) |||
    ((result.byte 2).toUInt64 <<< 16) |||
    ((result.byte 3).toUInt64 <<< 24) |||
    ((result.byte 4).toUInt64 <<< 32) |||
    ((result.byte 5).toUInt64 <<< 40) |||
    ((result.byte 6).toUInt64 <<< 48) |||
    ((result.byte 7).toUInt64 <<< 56)
  .ok ({ total := value, revision := 2 }, value)

end Examples.Near.NearMigration