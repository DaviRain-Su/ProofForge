import SolanaLean

namespace Examples.Vault

open SolanaLean.Runtime

/-- `shares` 的 hashed Map 用 slot 0 当 base。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def shareBase : UInt64 := 0

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- hashed `Map UInt64 UInt64` 读。 -/
@[solana_entry]
def getU64 (_s : State) (k : UInt64) : UInt64 :=
  evmMapGetU64 shareBase k

/-- hashed `Map UInt64 UInt64` 写。 -/
@[solana_entry]
def setU64 (_s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmMapSetU64 shareBase k v)
  else
    .error .overflow

/-- hashed `Map Addr20 UInt64` 读份额。 -/
@[solana_entry]
def shareOf (_s : State) (w0 w1 w2 : UInt64) : UInt64 :=
  evmMapGetAddr shareBase w0 w1 w2

/-- 把份额记到 Addr20。 -/
@[solana_entry]
def credit (_s : State) (w0 w1 w2 v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmMapSetAddr shareBase w0 w1 w2 v)
  else
    .error .overflow

/-- 封闭 ERC-20 `transfer`。 -/
@[solana_entry]
def pull (_s : State) (tw0 tw1 tw2 dw0 dw1 dw2 amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amt)
  else
    .error .overflow

/-- 封闭 ERC-20 `balanceOf(address(this))`。 -/
@[solana_entry]
def held (_s : State) (tw0 tw1 tw2 : UInt64) : UInt64 :=
  evmTokenBalanceOfSelf tw0 tw1 tw2

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Vault
