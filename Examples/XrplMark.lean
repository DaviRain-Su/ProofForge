import ProofForge

/-!
Zero-arg owner-gated SHA-512Half stamp for public AlphaNet.
`initialize` records the caller as owner. `stamp` requires
`Access.requireOwner` then writes `Hash.sha512HalfLit "vault"`.
No function parameters: AlphaNet public RPC 502s ContractCall Parameters.
-/
namespace Examples.XrplMark

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  hashed : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { owner0 := Context.callerW0, owner1 := Context.callerW1, owner2 := Context.callerW2,
    hashed := 0 }

/-- Owner-only: write SHA-512Half(`"vault"`) first little-endian u64. Not `sha256Lit`. -/
@[pf_entry]
def stamp (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
           hashed := Hash.sha512HalfLit "vault" }, (0 : UInt64))
  else
    .error .unauthorized

/-- Owner-only: zero the three owner limbs. Later stamps fail unauthorized. -/
@[pf_entry]
def renounce (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner (AccountId.ofLimbs s.owner0 s.owner1 s.owner2) then
    .ok ({ owner0 := 0, owner1 := 0, owner2 := 0, hashed := s.hashed }, (0 : UInt64))
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.hashed

end Examples.XrplMark
