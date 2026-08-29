import ProofForge.Evm.Sdk.Base

/-!
# EVM SDK bounded payment facades

Contract-facing names for the existing closed ETH, ERC-20, WETH, and fixed Uniswap V2 call
contracts. The target Runtime and `CallResult` interpreter still own CALL success and bounded
return-data validation; this module only defines reusable policy names and keeps applications away
from Runtime/ClosedCall/NativeFx implementation boundaries.

These facades do not open an arbitrary callee, selector, calldata buffer, return buffer,
`delegatecall`, or contract creation. `Ether.send` and the closed token calls revert when the
target contract fails their existing result policy. They also do not claim reentrancy protection:
applications must not infer lock ordering from a returned Lean state value.
-/

namespace ProofForge.Evm.Sdk

namespace Ether

/-- Require exact `msg.value == amount` on the current payable entry. -/
@[pf_inline] def accept (amount : UInt256) : UInt64 :=
  Runtime.evmDeposit256 amount

/-- Send bounded UInt256 wei to an explicit address; a failed CALL reverts. -/
@[pf_inline] def send (destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmSendEth256 destination amount

/-- Accept the current `msg.value` through the contract's no-calldata receive entry. -/
@[pf_inline] def receive : UInt64 := Runtime.evmReceive

end Ether

namespace ERC20

/-- Closed ERC-20 `transfer`; empty or canonical nonzero return data succeeds. -/
@[pf_inline] def transfer (token destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenTransfer token destination amount

/-- Closed ERC-20 `balanceOf(address(this))` with an exact UInt256 result. -/
@[pf_inline] def balanceOfSelf (token : Address) : UInt256 :=
  Runtime.evmTokenBalanceOfSelf token

/-- Closed ERC-20 `approve`; empty or canonical nonzero return data succeeds. -/
@[pf_inline] def approve (token spender : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenApprove token spender amount

/-- Closed ERC-20 `transferFrom`; empty or canonical nonzero return data succeeds. -/
@[pf_inline] def transferFrom (token owner destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenTransferFrom token owner destination amount

/-- Closed ERC-20 `allowance` with an exact UInt256 result. -/
@[pf_inline] def allowance (token owner spender : Address) : UInt256 :=
  Runtime.evmTokenAllowanceOf token owner spender

/-- Closed external EIP-2612 permit call. Signature validation belongs to the token callee. -/
@[pf_inline] def permit (token owner spender : Address) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : UInt64 :=
  Runtime.evmTokenPermit token owner spender value deadline v r s

end ERC20

namespace WETH

/-- Closed WETH `deposit()` with exact call value. -/
@[pf_inline] def deposit (weth : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmWethDeposit weth amount

/-- Closed WETH `withdraw(uint256)`. The application must expose an ETH receive path. -/
@[pf_inline] def withdraw (weth : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmWethWithdraw weth amount

end WETH

namespace UniswapV2

/-- Closed `swapExactTokensForTokens` with a two-token path. -/
@[pf_inline] def swapExact2 (router tokenA tokenB : Address)
    (amountIn minimumOut : UInt256) : UInt64 :=
  Runtime.evmSwapExact2 router tokenA tokenB amountIn minimumOut

/-- Closed `swapExactTokensForTokens` with a three-token path. -/
@[pf_inline] def swapExact3 (router tokenA tokenB tokenC : Address)
    (amountIn minimumOut : UInt256) : UInt64 :=
  Runtime.evmSwapExact3 router tokenA tokenB tokenC amountIn minimumOut

end UniswapV2


section Proofs

/-! ## facade 委托透明性定理

每个 `pf_inline` facade 恰好委托到对应的 Runtime 函数——
证明 facade 不改变语义，只是重命名。这是「使用 facade 与直接调 Runtime 等价」
的形式化表述。 -/

theorem accept_eq (amount : UInt256) :
    Ether.accept amount = Runtime.evmDeposit256 amount := rfl

theorem send_eq (destination : Address) (amount : UInt256) :
    Ether.send destination amount = Runtime.evmSendEth256 destination amount := rfl

theorem receive_eq : Ether.receive = Runtime.evmReceive := rfl

theorem transfer_eq (token destination : Address) (amount : UInt256) :
    ERC20.transfer token destination amount = Runtime.evmTokenTransfer token destination amount := rfl

theorem approve_eq (token spender : Address) (amount : UInt256) :
    ERC20.approve token spender amount = Runtime.evmTokenApprove token spender amount := rfl

theorem transferFrom_eq (token owner destination : Address) (amount : UInt256) :
    ERC20.transferFrom token owner destination amount
      = Runtime.evmTokenTransferFrom token owner destination amount := rfl

theorem balanceOfSelf_eq (token : Address) :
    ERC20.balanceOfSelf token = Runtime.evmTokenBalanceOfSelf token := rfl

theorem allowance_eq (token owner spender : Address) :
    ERC20.allowance token owner spender = Runtime.evmTokenAllowanceOf token owner spender := rfl

end Proofs

end ProofForge.Evm.Sdk
