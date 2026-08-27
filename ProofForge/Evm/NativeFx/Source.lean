import ProofForge.Attr
import ProofForge.Evm.Runtime

namespace ProofForge.Evm.NativeFx.Source

open ProofForge.Evm.Runtime

/--
Source-facing ETH, LOG, parameterized revert, and receive effects. `@[pf_inline]` erases these
helpers into the existing Runtime stubs and `Evm.NativeFx` component plan. No new Ops, IR, or
main-emitter case is introduced.
-/

@[pf_inline] def deposit (amt : UInt64) : UInt64 :=
  evmDeposit amt

@[pf_inline] def deposit256 (amt : UInt256) : UInt64 :=
  evmDeposit256 amt

@[pf_inline] def sendEth (dst : Addr20) (amt : UInt64) : UInt64 :=
  evmSendEth dst amt

@[pf_inline] def sendEth256 (dst : Addr20) (amt : UInt256) : UInt64 :=
  evmSendEth256 dst amt

@[pf_inline] def logTipped (amt : UInt64) : UInt64 :=
  evmLogTipped amt

@[pf_inline] def logIncremented (amt : UInt64) : UInt64 :=
  evmLogIncremented amt

@[pf_inline] def logTransfer (amt : UInt64) : UInt64 :=
  evmLogTransfer amt

@[pf_inline] def logApproval (amt : UInt64) : UInt64 :=
  evmLogApproval amt

@[pf_inline] def logTransfer256 (src dest : Addr20) (amt : UInt256) : UInt64 :=
  evmLogTransfer256 src dest amt

@[pf_inline] def logApproval256 (owner spender : Addr20) (amt : UInt256) : UInt64 :=
  evmLogApproval256 owner spender amt

@[pf_inline] def revertInsufficient (held want : UInt256) : UInt64 :=
  evmRevertInsufficient held want

@[pf_inline] def revertUnauthorized (who : Addr20) : UInt64 :=
  evmRevertUnauthorized who

@[pf_inline] def revertZeroAddress : UInt64 :=
  evmRevertZeroAddress

@[pf_inline] def receive : UInt64 :=
  evmReceive

end ProofForge.Evm.NativeFx.Source
