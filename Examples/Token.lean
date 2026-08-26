import ProofForge

namespace Examples.Token

open ProofForge.Evm.Runtime

/-- dummy 占槽；余额和额度走 hashed map。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def balBase : UInt64 := 0
def allowBase : UInt64 := 1
def nonceBase : UInt64 := 2

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给 Addr20 记 256-bit 余额。测试用铸币，不是权限模型。 -/
@[pf_entry]
def mint (_s : State) (to : Addr20) (v : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := evmMapSetAddr256 balBase to v },
      evmLogTransfer256 ⟨0, 0, 0⟩ to v)
  else
    .error .overflow

@[pf_entry]
def balanceOf (_s : State) (who : Addr20) : UInt256 :=
  evmMapGetAddr256 balBase who

@[pf_entry]
def allowanceOf (_s : State) (owner spender : Addr20) : UInt256 :=
  evmMapGetPair256 allowBase owner spender

@[pf_entry]
def nonceOf (_s : State) (who : Addr20) : UInt256 :=
  evmMapGetAddr256 nonceBase who

/-- 封闭 EIP-2612 `permit`。name=`Token`，version=`1`。 -/
@[pf_entry]
def permit (_s : State) (owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmPermit owner spender value deadline v r s)
  else
    .error .overflow

/-- caller → spender 写额度，并 LOG3 `Approval(address,address,uint256)`。 -/
@[pf_entry]
def approve (_s : State) (spender : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy :=
        evmMapSetPair256 allowBase evmCaller20 spender amt },
      evmLogApproval256 evmCaller20 spender amt)
  else
    .error .overflow

/-- 从 caller 扣、给 dest 加。不足 → `Insufficient(have,want)`。 -/
@[pf_entry]
def transfer (_s : State) (dest : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if evmGe256 (evmMapGetAddr256 balBase evmCaller20) amt then
    .ok ({ dummy :=
        (evmMapSetAddr256 balBase evmCaller20
          (evmSub256 (evmMapGetAddr256 balBase evmCaller20) amt)) |||
        (evmMapSetAddr256 balBase dest
          (evmAdd256 (evmMapGetAddr256 balBase dest) amt)) },
      evmLogTransfer256 evmCaller20 dest amt)
  else
    .ok ({ dummy := 0 },
      evmRevertInsufficient (evmMapGetAddr256 balBase evmCaller20) amt)

/-- 查 pair 额度；不足 → `Insufficient`。成功则改余额并写剩余额度。 -/
@[pf_entry]
def transferFrom (_s : State) (owner dest : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if evmGe256 (evmMapGetPair256 allowBase owner evmCaller20) amt then
    if evmGe256 (evmMapGetAddr256 balBase owner) amt then
      .ok ({ dummy :=
          (evmMapSetAddr256 balBase owner
            (evmSub256 (evmMapGetAddr256 balBase owner) amt)) |||
          (evmMapSetAddr256 balBase dest
            (evmAdd256 (evmMapGetAddr256 balBase dest) amt)) |||
          (evmMapSetPair256 allowBase owner evmCaller20
            (evmSub256 (evmMapGetPair256 allowBase owner evmCaller20) amt)) },
        evmLogTransfer256 owner dest amt)
    else
      .ok ({ dummy := 0 },
        evmRevertInsufficient (evmMapGetAddr256 balBase owner) amt)
  else
    .ok ({ dummy := 0 },
      evmRevertInsufficient (evmMapGetPair256 allowBase owner evmCaller20) amt)

/-- LOG1 `Transfer(uint64)`。 -/
@[pf_entry]
def logXfer (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmLogTransfer amt)
  else
    .error .overflow

/-- LOG1 `Approval(uint64)`。 -/
@[pf_entry]
def logApprove (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmLogApproval amt)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Token
