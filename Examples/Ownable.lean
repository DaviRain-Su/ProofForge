import ProofForge.Evm.Sdk

namespace Examples.Ownable

open ProofForge.Evm.Sdk

/-- owner 是构造期 immutable；storage 只留计数。allowance 走 checked UInt256 pair ledger。 -/
structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def allowances : Fungible.Allowances :=
  Storage.Layout.root.addressPairMap256.handle

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (_owner : Address) : State :=
  { value := 0 }

/-- 只有构造期 owner 能加。非 owner → `Unauthorized(caller)`。整值比较由 SDK Address 拥有。 -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if s.value ≤ u64Max - delta then
      let next := s.value + delta
      .ok ({ value := next }, next)
    else
      .error .overflow
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- `who` 是零地址 → `ZeroAddress()`。成功只回 `who.w0`，不改 storage。 -/
@[pf_entry]
def guardZero (s : State) (who : Address) : Except Error (State × UInt64) :=
  if Address.isZero who then
    .ok (s, Revert.zeroAddress)
  else
    .ok (s, who.w0)

/-- LOG1 `Incremented(uint64)`。 -/
@[pf_entry]
def logInc (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ value := 0 }, Event.incremented amt)
  else
    .error .overflow

/-- pair-key `approve(owner, spender) = amt`。 -/
@[pf_entry]
def approve (_s : State) (owner spender : Address) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ value := 0 }, Fungible.Allowances.approve allowances owner spender amt)
  else
    .error .overflow

/-- Checked delegated allowance consumption. -/
@[pf_entry]
def spend (_s : State) (owner spender : Address) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if Fungible.Allowances.canSpend allowances owner spender amt then
    .ok ({ value := 0 }, Fungible.Allowances.spend allowances owner spender amt)
  else
    .ok ({ value := 0 }, Fungible.Allowances.insufficient allowances owner spender amt)

@[pf_entry]
def allowance (_s : State) (owner spender : Address) : UInt256 :=
  Fungible.Allowances.allowanceOf allowances owner spender

@[pf_entry]
def ownerOf (_s : State) : Address :=
  Immutable.address

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Ownable
