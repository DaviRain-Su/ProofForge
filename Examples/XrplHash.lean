import ProofForge

namespace Examples.XrplHash

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  hashed : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { hashed := 0 }

/-- 把 SHA-512Half(`"vault"`) 的第一个小端 u64 写入槽。不是 `sha256Lit`。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ hashed := Hash.sha512HalfLit "vault" }, (0 : UInt64))
  else
    .error .overflow

/-- view：槽值。本宿主不填 `meta.ReturnValue`，工程门读 ContractJson。 -/
@[pf_entry]
def get (s : State) : UInt64 :=
  s.hashed

end Examples.XrplHash
