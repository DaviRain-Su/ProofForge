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

end ProofForge.Evm.Sdk
