import ProofForge

namespace Examples.Token

open ProofForge.Evm.Runtime
open ProofForge.Evm.HashedMap.Source
open ProofForge.Evm

/-- dummy 占槽；paused 是 UInt8（0 运行，1 暂停）；supply 是账户里的 UInt256；
    余额和额度走 hashed map。owner 是构造期 immutable。 -/
structure State where
  dummy : UInt64
  paused : UInt8
  supply : UInt256
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def balances : MapAddr256 := { base := 0 }
@[pf_inline] def allowances : MapPair256 := { base := 1 }
@[pf_inline] def nonces : MapAddr256 := { base := 2 }

@[pf_entry]
def init (_owner : Addr20) : State :=
  { dummy := 0, paused := 0, supply := ⟨0, 0, 0, 0⟩ }

/-- 给 Addr20 记 256-bit 余额，并累加 totalSupply。只有构造期 owner 能铸。
    非 owner → `Unauthorized(caller)`；paused → `Paused()`；`to` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def mint (s : State) (to : Addr20) (v : UInt256) : Except Error (State × UInt64) :=
  if WideWord.Source.eqImm20 evmCaller20 then
    if s.paused != 0 then
      .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
        NativeFx.Source.revertPaused)
    else if WideWord.Source.isZero20 to then
      .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
        NativeFx.Source.revertZeroAddress)
    else if (0 : UInt64) ≠ 1 then
      .ok ({ dummy := setAddr256 balances to v, paused := s.paused,
             supply := WideWord.Source.add s.supply v },
        NativeFx.Source.logTransfer256 WideWord.Source.zero20 to v)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertUnauthorized evmCaller20)

@[pf_entry]
def balanceOf (_s : State) (who : Addr20) : UInt256 :=
  getAddr256 balances who

/-- 账户里的总量。mint 累加；burn 相减；transfer 不动。 -/
@[pf_entry]
def totalSupply (s : State) : UInt256 :=
  s.supply

/-- 编译期 `decimals()`。不是 storage，也不是动态 string。 -/
@[pf_entry]
def decimals (_s : State) : UInt8 :=
  18

/-- 编译期 `name()`，右填充 ASCII `"Token"`。不是动态 string。 -/
@[pf_entry]
def name (_s : State) : Bytes32 :=
  ⟨0x546f6b656e, 0, 0, 0⟩

/-- 编译期 `symbol()`，右填充 ASCII `"PF"`。不是动态 string。 -/
@[pf_entry]
def symbol (_s : State) : Bytes32 :=
  ⟨0x5046, 0, 0, 0⟩

@[pf_entry]
def allowanceOf (_s : State) (owner spender : Addr20) : UInt256 :=
  getPair256 allowances owner spender

@[pf_entry]
def nonceOf (_s : State) (who : Addr20) : UInt256 :=
  getAddr256 nonces who

/-- 封闭 EIP-712 domain separator。name=`Token`，version=`1`。 -/
@[pf_entry]
def DOMAIN_SEPARATOR (_s : State) : Bytes32 :=
  ClosedCall.Source.domainSeparator

/-- 封闭 EIP-2612 `permit`。name=`Token`，version=`1`。
    paused → `Paused()`。 -/
@[pf_entry]
def permit (st : State) (owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r sig : Bytes32) : Except Error (State × UInt64) :=
  if st.paused != 0 then
    .ok ({ dummy := st.dummy, paused := st.paused, supply := st.supply },
      NativeFx.Source.revertPaused)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := st.dummy, paused := st.paused, supply := st.supply },
      ClosedCall.Source.permit owner spender value deadline v r sig)
  else
    .error .overflow

/-- caller → spender 写额度，并 LOG3 `Approval(address,address,uint256)`。
    paused → `Paused()`；`spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def approve (s : State) (spender : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 spender then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy :=
        setPair256 allowances evmCaller20 spender amt, paused := s.paused, supply := s.supply },
      NativeFx.Source.logApproval256 evmCaller20 spender amt)
  else
    .error .overflow

/-- caller → spender 现额度加上 `added`，并 LOG3 Approval。溢出 revert。
    paused → `Paused()`；`spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def increaseAllowance (s : State) (spender : Addr20) (added : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 spender then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if (0 : UInt64) ≠ 1 then
    let next := nextAddPair256 allowances evmCaller20 spender added
    .ok ({ dummy := setPair256 allowances evmCaller20 spender next,
           paused := s.paused, supply := s.supply },
      NativeFx.Source.logApproval256 evmCaller20 spender next)
  else
    .error .overflow

/-- caller → spender 现额度减去 `subtracted`。不够 → `Insufficient(have,want)`。
    paused → `Paused()`；`spender` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def decreaseAllowance (s : State) (spender : Addr20) (subtracted : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 spender then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if gePair256 allowances evmCaller20 spender subtracted then
    let next := nextSubPair256 allowances evmCaller20 spender subtracted
    .ok ({ dummy := setPair256 allowances evmCaller20 spender next,
           paused := s.paused, supply := s.supply },
      NativeFx.Source.logApproval256 evmCaller20 spender next)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      revertInsufficientPair256 allowances evmCaller20 spender subtracted)

/-- 从 caller 扣余额并减 totalSupply。不足 → `Insufficient(have,want)`。
    paused → `Paused()`。 -/
@[pf_entry]
def burn (s : State) (amt : UInt256) : Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if geAddr256 balances evmCaller20 amt then
    let debit :=
      setAddr256 balances evmCaller20
        (nextSubAddr256 balances evmCaller20 amt)
    .ok ({ dummy := debit, paused := s.paused, supply := WideWord.Source.sub s.supply amt },
      NativeFx.Source.logTransfer256 evmCaller20 WideWord.Source.zero20 amt)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      revertInsufficientAddr256 balances evmCaller20 amt)

/-- caller 用额度烧掉 owner 的币。额度或余额不够 → `Insufficient`。
    paused → `Paused()`；`owner` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def burnFrom (s : State) (owner : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 owner then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if gePair256 allowances owner evmCaller20 amt then
    if geAddr256 balances owner amt then
      let debit :=
        (setAddr256 balances owner
          (nextSubAddr256 balances owner amt)) |||
        (setPair256 allowances owner evmCaller20
          (nextSubPair256 allowances owner evmCaller20 amt))
      .ok ({ dummy := debit, paused := s.paused, supply := WideWord.Source.sub s.supply amt },
        NativeFx.Source.logTransfer256 owner WideWord.Source.zero20 amt)
    else
      .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
        revertInsufficientAddr256 balances owner amt)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      revertInsufficientPair256 allowances owner evmCaller20 amt)

/-- 从 caller 扣、给 dest 加。不足 → `Insufficient(have,want)`。
    paused → `Paused()`；`dest` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def transfer (s : State) (dest : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 dest then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if geAddr256 balances evmCaller20 amt then
    let debit :=
      (setAddr256 balances evmCaller20
        (nextSubAddr256 balances evmCaller20 amt)) |||
      (setAddr256 balances dest
        (nextAddAddr256 balances dest amt))
    .ok ({ dummy := debit, paused := s.paused, supply := s.supply },
      NativeFx.Source.logTransfer256 evmCaller20 dest amt)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      revertInsufficientAddr256 balances evmCaller20 amt)

/-- 查 pair 额度；不足 → `Insufficient`。成功则改余额并写剩余额度。
    paused → `Paused()`；`dest` 为零地址 → `ZeroAddress()`。 -/
@[pf_entry]
def transferFrom (s : State) (owner dest : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertPaused)
  else if WideWord.Source.isZero20 dest then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.revertZeroAddress)
  else if gePair256 allowances owner evmCaller20 amt then
    if geAddr256 balances owner amt then
      let debit :=
        (setAddr256 balances owner
          (nextSubAddr256 balances owner amt)) |||
        (setAddr256 balances dest
          (nextAddAddr256 balances dest amt)) |||
        (setPair256 allowances owner evmCaller20
          (nextSubPair256 allowances owner evmCaller20 amt))
      .ok ({ dummy := debit, paused := s.paused, supply := s.supply },
        NativeFx.Source.logTransfer256 owner dest amt)
    else
      .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
        revertInsufficientAddr256 balances owner amt)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      revertInsufficientPair256 allowances owner evmCaller20 amt)

/-- 只有构造期 owner 能暂停。非 owner → `Unauthorized(caller)`。 -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if WideWord.Source.eqImm20 evmCaller20 then
    if (0 : UInt64) ≠ 1 then
      .ok ({ dummy := s.dummy, paused := 1, supply := s.supply }, 1)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertUnauthorized evmCaller20)

/-- 只有构造期 owner 能恢复。非 owner → `Unauthorized(caller)`。 -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if WideWord.Source.eqImm20 evmCaller20 then
    if (0 : UInt64) ≠ 1 then
      .ok ({ dummy := s.dummy, paused := 0, supply := s.supply }, 0)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply },
      NativeFx.Source.revertUnauthorized evmCaller20)

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

@[pf_entry]
def ownerOf (_s : State) : Addr20 :=
  evmImm20

/-- LOG1 `Transfer(uint64)`。工程入口，不受 pause。 -/
@[pf_entry]
def logXfer (s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.logTransfer amt)
  else
    .error .overflow

/-- LOG1 `Approval(uint64)`。 -/
@[pf_entry]
def logApprove (s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, paused := s.paused, supply := s.supply }, NativeFx.Source.logApproval amt)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Token
