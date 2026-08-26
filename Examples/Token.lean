import ProofForge

namespace Examples.Token

open ProofForge.Evm.Runtime

/-- dummy 占槽；余额和额度走 hashed map。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | insufficient
  deriving Repr, DecidableEq, Inhabited, BEq

def balBase : UInt64 := 0
def allowBase : UInt64 := 1
def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给 Addr20 记余额。测试用铸币，不是权限模型。 -/
@[pf_entry]
def mint (_s : State) (to : Addr20) (v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmMapSetAddr balBase to v)
  else
    .error .overflow

@[pf_entry]
def balanceOf (_s : State) (who : Addr20) : UInt64 :=
  evmMapGetAddr balBase who

@[pf_entry]
def allowanceOf (_s : State) (owner spender : Addr20) : UInt64 :=
  evmMapGetPair allowBase owner spender

/-- caller → spender 写额度，并 LOG `Approval(uint64)`。 -/
@[pf_entry]
def approve (_s : State) (spender : Addr20) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy :=
        evmMapSetPair allowBase evmCaller20 spender amt },
      evmLogApproval amt)
  else
    .error .overflow

/-- 从 caller 扣、给 dest 加。不足 → `insufficient`。 -/
@[pf_entry]
def transfer (_s : State) (dest : Addr20) (amt : UInt64) : Except Error (State × UInt64) :=
  if evmMapGetAddr balBase evmCaller20 ≥ amt then
    .ok ({ dummy :=
        (evmMapSetAddr balBase evmCaller20
          (evmMapGetAddr balBase evmCaller20 - amt)) |||
        (evmMapSetAddr balBase dest
          (evmMapGetAddr balBase dest + amt)) },
      evmLogTransfer amt)
  else
    .error .insufficient

/-- 查 pair 额度；不足 → `insufficient`。成功则改余额并写剩余额度。 -/
@[pf_entry]
def transferFrom (_s : State) (owner dest : Addr20) (amt : UInt64) :
    Except Error (State × UInt64) :=
  if evmMapGetPair allowBase owner evmCaller20 ≥ amt then
    if evmMapGetAddr balBase owner ≥ amt then
      .ok ({ dummy :=
          (evmMapSetAddr balBase owner
            (evmMapGetAddr balBase owner - amt)) |||
          (evmMapSetAddr balBase dest
            (evmMapGetAddr balBase dest + amt)) |||
          (evmMapSetPair allowBase owner evmCaller20
            (evmMapGetPair allowBase owner evmCaller20 - amt)) },
        evmLogTransfer amt)
    else
      .error .insufficient
  else
    .error .insufficient

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
