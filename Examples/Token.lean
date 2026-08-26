import ProofForge

namespace Examples.Token

open ProofForge.Evm.Runtime

/-- dummy 占槽；supply 是账户里的 UInt256；余额和额度走 hashed map。 -/
structure State where
  dummy : UInt64
  supply : UInt256
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def balBase : UInt64 := 0
def allowBase : UInt64 := 1
def nonceBase : UInt64 := 2

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0, supply := ⟨0, 0, 0, 0⟩ }

/-- 给 Addr20 记 256-bit 余额，并累加 totalSupply。测试用铸币，不是权限模型。
    `to` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def mint (s : State) (to : Addr20) (v : UInt256) : Except Error (State × UInt64) :=
  if evmEq20 to ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := evmMapSetAddr256 balBase to v,
           supply := evmAdd256 s.supply v },
      evmLogTransfer256 ⟨0, 0, 0⟩ to v)
  else
    .error .overflow

@[pf_entry]
def balanceOf (_s : State) (who : Addr20) : UInt256 :=
  evmMapGetAddr256 balBase who

/-- 账户里的总量。mint 累加；burn 相减；transfer 不动。 -/
@[pf_entry]
def totalSupply (s : State) : UInt256 :=
  s.supply

/-- 编译期 `decimals()`。不是 storage，也不是动态 string。 -/
@[pf_entry]
def decimals (_s : State) : UInt8 :=
  18

@[pf_entry]
def allowanceOf (_s : State) (owner spender : Addr20) : UInt256 :=
  evmMapGetPair256 allowBase owner spender

@[pf_entry]
def nonceOf (_s : State) (who : Addr20) : UInt256 :=
  evmMapGetAddr256 nonceBase who

/-- 封闭 EIP-712 domain separator。name=`Token`，version=`1`。 -/
@[pf_entry]
def DOMAIN_SEPARATOR (_s : State) : Bytes32 :=
  evmDomainSeparator

/-- 封闭 EIP-2612 `permit`。name=`Token`，version=`1`。 -/
@[pf_entry]
def permit (st : State) (owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r sig : Bytes32) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := st.dummy, supply := st.supply }, evmPermit owner spender value deadline v r sig)
  else
    .error .overflow

/-- caller → spender 写额度，并 LOG3 `Approval(address,address,uint256)`。
    `spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def approve (s : State) (spender : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if evmEq20 spender ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy :=
        evmMapSetPair256 allowBase evmCaller20 spender amt, supply := s.supply },
      evmLogApproval256 evmCaller20 spender amt)
  else
    .error .overflow

/-- caller → spender 现额度加上 `added`，并 LOG3 Approval。溢出 revert。
    `spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def increaseAllowance (s : State) (spender : Addr20) (added : UInt256) :
    Except Error (State × UInt64) :=
  if evmEq20 spender ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if (0 : UInt64) ≠ 1 then
    let next := evmAdd256 (evmMapGetPair256 allowBase evmCaller20 spender) added
    .ok ({ dummy := evmMapSetPair256 allowBase evmCaller20 spender next,
           supply := s.supply },
      evmLogApproval256 evmCaller20 spender next)
  else
    .error .overflow

/-- caller → spender 现额度减去 `subtracted`。不够 → `Insufficient(have,want)`。
    `spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def decreaseAllowance (s : State) (spender : Addr20) (subtracted : UInt256) :
    Except Error (State × UInt64) :=
  if evmEq20 spender ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if evmGe256 (evmMapGetPair256 allowBase evmCaller20 spender) subtracted then
    let next := evmSub256 (evmMapGetPair256 allowBase evmCaller20 spender) subtracted
    .ok ({ dummy := evmMapSetPair256 allowBase evmCaller20 spender next,
           supply := s.supply },
      evmLogApproval256 evmCaller20 spender next)
  else
    .ok ({ dummy := s.dummy, supply := s.supply },
      evmRevertInsufficient (evmMapGetPair256 allowBase evmCaller20 spender) subtracted)

/-- 从 caller 扣余额并减 totalSupply。不足 → `Insufficient(have,want)`。 -/
@[pf_entry]
def burn (s : State) (amt : UInt256) : Except Error (State × UInt64) :=
  if evmGe256 (evmMapGetAddr256 balBase evmCaller20) amt then
    let debit :=
      evmMapSetAddr256 balBase evmCaller20
        (evmSub256 (evmMapGetAddr256 balBase evmCaller20) amt)
    .ok ({ dummy := debit, supply := evmSub256 s.supply amt },
      evmLogTransfer256 evmCaller20 ⟨0, 0, 0⟩ amt)
  else
    .ok ({ dummy := s.dummy, supply := s.supply },
      evmRevertInsufficient (evmMapGetAddr256 balBase evmCaller20) amt)

/-- caller 用额度烧掉 owner 的币。额度或余额不够 → `Insufficient`。
    `owner` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def burnFrom (s : State) (owner : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if evmEq20 owner ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if evmGe256 (evmMapGetPair256 allowBase owner evmCaller20) amt then
    if evmGe256 (evmMapGetAddr256 balBase owner) amt then
      let debit :=
        (evmMapSetAddr256 balBase owner
          (evmSub256 (evmMapGetAddr256 balBase owner) amt)) |||
        (evmMapSetPair256 allowBase owner evmCaller20
          (evmSub256 (evmMapGetPair256 allowBase owner evmCaller20) amt))
      .ok ({ dummy := debit, supply := evmSub256 s.supply amt },
        evmLogTransfer256 owner ⟨0, 0, 0⟩ amt)
    else
      .ok ({ dummy := s.dummy, supply := s.supply },
        evmRevertInsufficient (evmMapGetAddr256 balBase owner) amt)
  else
    .ok ({ dummy := s.dummy, supply := s.supply },
      evmRevertInsufficient (evmMapGetPair256 allowBase owner evmCaller20) amt)

/-- 从 caller 扣、给 dest 加。不足 → `Insufficient(have,want)`。
    `dest` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def transfer (s : State) (dest : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if evmEq20 dest ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if evmGe256 (evmMapGetAddr256 balBase evmCaller20) amt then
    let debit :=
      (evmMapSetAddr256 balBase evmCaller20
        (evmSub256 (evmMapGetAddr256 balBase evmCaller20) amt)) |||
      (evmMapSetAddr256 balBase dest
        (evmAdd256 (evmMapGetAddr256 balBase dest) amt))
    .ok ({ dummy := debit, supply := s.supply },
      evmLogTransfer256 evmCaller20 dest amt)
  else
    .ok ({ dummy := s.dummy, supply := s.supply },
      evmRevertInsufficient (evmMapGetAddr256 balBase evmCaller20) amt)

/-- 查 pair 额度；不足 → `Insufficient`。成功则改余额并写剩余额度。
    `dest` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def transferFrom (s : State) (owner dest : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if evmEq20 dest ⟨0, 0, 0⟩ then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmRevertZeroAddress)
  else if evmGe256 (evmMapGetPair256 allowBase owner evmCaller20) amt then
    if evmGe256 (evmMapGetAddr256 balBase owner) amt then
      let debit :=
        (evmMapSetAddr256 balBase owner
          (evmSub256 (evmMapGetAddr256 balBase owner) amt)) |||
        (evmMapSetAddr256 balBase dest
          (evmAdd256 (evmMapGetAddr256 balBase dest) amt)) |||
        (evmMapSetPair256 allowBase owner evmCaller20
          (evmSub256 (evmMapGetPair256 allowBase owner evmCaller20) amt))
      .ok ({ dummy := debit, supply := s.supply },
        evmLogTransfer256 owner dest amt)
    else
      .ok ({ dummy := s.dummy, supply := s.supply },
        evmRevertInsufficient (evmMapGetAddr256 balBase owner) amt)
  else
    .ok ({ dummy := s.dummy, supply := s.supply },
      evmRevertInsufficient (evmMapGetPair256 allowBase owner evmCaller20) amt)

/-- LOG1 `Transfer(uint64)`。 -/
@[pf_entry]
def logXfer (s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmLogTransfer amt)
  else
    .error .overflow

/-- LOG1 `Approval(uint64)`。 -/
@[pf_entry]
def logApprove (s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, supply := s.supply }, evmLogApproval amt)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Token
