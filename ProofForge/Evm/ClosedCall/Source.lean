import ProofForge.Attr
import ProofForge.Evm.Runtime

namespace ProofForge.Evm.ClosedCall.Source

open ProofForge.Evm.Runtime

/--
Source-facing closed ERC-20 / WETH / Uniswap / permit calls. Dynamic addresses and amounts stay
in the arguments; `@[pf_inline]` erases these helpers into the existing Runtime stubs and
`Evm.ClosedCall` component plan. No new Ops, IR, or main-emitter case is introduced.
-/

@[pf_inline] def transfer (token dest : Addr20) (amt : UInt256) : UInt64 :=
  evmTokenTransfer token dest amt

@[pf_inline] def balanceOfSelf (token : Addr20) : UInt256 :=
  evmTokenBalanceOfSelf token

@[pf_inline] def approve (token spender : Addr20) (amt : UInt256) : UInt64 :=
  evmTokenApprove token spender amt

@[pf_inline] def transferFrom (token owner dest : Addr20) (amt : UInt256) : UInt64 :=
  evmTokenTransferFrom token owner dest amt

@[pf_inline] def allowanceOf (token owner spender : Addr20) : UInt256 :=
  evmTokenAllowanceOf token owner spender

@[pf_inline] def wethDeposit (weth : Addr20) (amt : UInt256) : UInt64 :=
  evmWethDeposit weth amt

@[pf_inline] def wethWithdraw (weth : Addr20) (amt : UInt256) : UInt64 :=
  evmWethWithdraw weth amt

@[pf_inline] def swapExact2 (router tokenA tokenB : Addr20) (amtIn minOut : UInt256) : UInt64 :=
  evmSwapExact2 router tokenA tokenB amtIn minOut

@[pf_inline] def swapExact3 (router tokenA tokenB tokenC : Addr20)
    (amtIn minOut : UInt256) : UInt64 :=
  evmSwapExact3 router tokenA tokenB tokenC amtIn minOut

@[pf_inline] def permit (owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : UInt64 :=
  evmPermit owner spender value deadline v r s

@[pf_inline] def tokenPermit (token owner spender : Addr20) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : UInt64 :=
  evmTokenPermit token owner spender value deadline v r s

@[pf_inline] def domainSeparator : Bytes32 :=
  evmDomainSeparator

end ProofForge.Evm.ClosedCall.Source
