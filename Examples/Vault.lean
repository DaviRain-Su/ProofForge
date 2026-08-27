import ProofForge

namespace Examples.Vault

open ProofForge.Evm.Runtime
open ProofForge.Evm.HashedMap.Source
open ProofForge.Evm.ClosedCall.Source
open ProofForge.Evm

/-- `shares` 的 hashed Map 用 slot 0 当 base。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def keys : MapU64 := { base := 0 }
@[pf_inline] def shares : MapAddr256 := { base := 0 }

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- hashed `Map UInt64 UInt64` 读。 -/
@[pf_entry]
def getU64 (_s : State) (k : UInt64) : UInt64 :=
  HashedMap.Source.getU64 keys k

/-- hashed `Map UInt64 UInt64` 写。 -/
@[pf_entry]
def setU64 (_s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, HashedMap.Source.setU64 keys k v)
  else
    .error .overflow

/-- hashed `Map Addr20 UInt256` 读份额。 -/
@[pf_entry]
def shareOf (_s : State) (who : Addr20) : UInt256 :=
  getAddr256 shares who

/-- 把 256-bit 份额记到 Addr20。 -/
@[pf_entry]
def credit (_s : State) (who : Addr20) (v : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, setAddr256 shares who v)
  else
    .error .overflow

/-- 封闭 ERC-20 `transfer(address,uint256)`。 -/
@[pf_entry]
def pull (_s : State) (token dest : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.transfer token dest amt)
  else
    .error .overflow

/-- 封闭 ERC-20 `balanceOf(address(this))`。 -/
@[pf_entry]
def held (_s : State) (token : Addr20) : UInt256 :=
  ClosedCall.Source.balanceOfSelf token

/-- 封闭 ERC-20 `approve(address,uint256)`。 -/
@[pf_entry]
def grant (_s : State) (token spender : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.approve token spender amt)
  else
    .error .overflow

/-- 封闭外部 EIP-2612 `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`。 -/
@[pf_entry]
def permit (_s : State) (token owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.tokenPermit token owner spender value deadline v r s)
  else
    .error .overflow

/-- 封闭 ERC-20 `transferFrom(address,address,uint256)`。 -/
@[pf_entry]
def take (_s : State) (token owner dest : Addr20) (amt : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.transferFrom token owner dest amt)
  else
    .error .overflow

/-- 封闭 ERC-20 `allowance(owner,spender)`。 -/
@[pf_entry]
def allowed (_s : State) (token owner spender : Addr20) : UInt256 :=
  ClosedCall.Source.allowanceOf token owner spender

/-- 无 calldata 的 payable `receive()`。WETH `withdraw` 把 ETH 打回来时需要。 -/
@[pf_entry]
def receive (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, NativeFx.Source.receive)
  else
    .error .overflow

/-- 封闭 WETH `deposit()`。入口 payable：先 `eq(callvalue(), amt)`，再 value CALL。 -/
@[pf_entry]
def wrap (_s : State) (weth : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := NativeFx.Source.deposit256 amt }, ClosedCall.Source.wethDeposit weth amt)
  else
    .error .overflow

/-- 封闭 WETH `withdraw(uint256)`。ETH 回到本合约。 -/
@[pf_entry]
def unwrap (_s : State) (weth : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.wethWithdraw weth amt)
  else
    .error .overflow

/-- 封闭 Uniswap V2 `swapExactTokensForTokens`，path 长度 2。 -/
@[pf_entry]
def swap2 (_s : State) (router tokenA tokenB : Addr20) (amtIn minOut : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.swapExact2 router tokenA tokenB amtIn minOut)
  else
    .error .overflow

/-- 封闭 Uniswap V2 `swapExactTokensForTokens`，path 长度 3。 -/
@[pf_entry]
def swap3 (_s : State) (router tokenA tokenB tokenC : Addr20) (amtIn minOut : UInt256) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, ClosedCall.Source.swapExact3 router tokenA tokenB tokenC amtIn minOut)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Vault
