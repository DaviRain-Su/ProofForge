import ProofForge

namespace Examples.Ownable

open ProofForge.Evm.Runtime

/-- owner 一颗 Addr20（storage 三槽）+ 一个计数。allowance 走 hashed pair map。 -/
structure State where
  owner : Addr20
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

/-- pair-key Map 的 hashed base。抽出认这个名字。 -/
def allowBase : UInt64 := 0

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (owner : Addr20) : State :=
  { owner := owner, value := 0 }

/-- 只有 owner 能加。非 owner → `unauthorized`。身份比三叶，不把 Addr20 当单一 UInt64。 -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if evmCaller20.w0 = s.owner.w0 then
    if evmCaller20.w1 = s.owner.w1 then
      if evmCaller20.w2 = s.owner.w2 then
        if s.value ≤ u64Max - delta then
          let next := s.value + delta
          .ok ({ owner := s.owner, value := next }, next)
        else
          .error .overflow
      else
        .error .unauthorized
    else
      .error .unauthorized
  else
    .error .unauthorized

/-- LOG1 `Incremented(uint64)`。 -/
@[pf_entry]
def logInc (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner := ⟨0, 0, 0⟩, value := 0 }, evmLogIncremented amt)
  else
    .error .overflow

/-- pair-key `approve(owner, spender) = amt`。 -/
@[pf_entry]
def approve (_s : State) (owner spender : Addr20) (amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner := ⟨0, 0, 0⟩, value := 0 },
      evmMapSetPair allowBase owner spender amt)
  else
    .error .overflow

/-- 把 pair-key 额度写成 `amt`。不是 ERC-20 `transferFrom` 减法。 -/
@[pf_entry]
def spend (_s : State) (owner spender : Addr20) (amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner := ⟨0, 0, 0⟩, value := 0 },
      evmMapSetPair allowBase owner spender amt)
  else
    .error .overflow

@[pf_entry]
def allowance (_s : State) (owner spender : Addr20) : UInt64 :=
  evmMapGetPair allowBase owner spender

@[pf_entry]
def ownerOf (s : State) : Addr20 :=
  s.owner

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Ownable
