import ProofForge

namespace Examples.Ownable

open ProofForge.Evm.Runtime

/-- owner 是构造期 immutable；storage 只留计数。allowance 走 hashed pair map。 -/
structure State where
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
def init (_owner : Addr20) : State :=
  { value := 0 }

/-- 只有构造期 owner 能加。非 owner → `Unauthorized(caller)`。整值 `evmEq20`。 -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if evmEq20 evmCaller20 evmImm20 then
    if s.value ≤ u64Max - delta then
      let next := s.value + delta
      .ok ({ value := next }, next)
    else
      .error .overflow
  else
    .ok (s, evmRevertUnauthorized evmCaller20)

/-- `who` 是零地址 → `ZeroAddress()`。成功只回 `who.w0`，不改 storage。 -/
@[pf_entry]
def guardZero (s : State) (who : Addr20) : Except Error (State × UInt64) :=
  if evmEq20 who ⟨0, 0, 0⟩ then
    .ok (s, evmRevertZeroAddress)
  else
    .ok (s, who.w0)

/-- LOG1 `Incremented(uint64)`。 -/
@[pf_entry]
def logInc (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ value := 0 }, evmLogIncremented amt)
  else
    .error .overflow

/-- pair-key `approve(owner, spender) = amt`。 -/
@[pf_entry]
def approve (_s : State) (owner spender : Addr20) (amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ value := 0 },
      evmMapSetPair allowBase owner spender amt)
  else
    .error .overflow

/-- 把 pair-key 额度写成 `amt`。不是 ERC-20 `transferFrom` 减法。 -/
@[pf_entry]
def spend (_s : State) (owner spender : Addr20) (amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ value := 0 },
      evmMapSetPair allowBase owner spender amt)
  else
    .error .overflow

@[pf_entry]
def allowance (_s : State) (owner spender : Addr20) : UInt64 :=
  evmMapGetPair allowBase owner spender

@[pf_entry]
def ownerOf (_s : State) : Addr20 :=
  evmImm20

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Ownable
