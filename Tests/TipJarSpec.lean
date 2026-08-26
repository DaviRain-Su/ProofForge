import Examples.TipJar

namespace Tests.TipJarSpec

open Examples.TipJar
open ProofForge.Evm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard chainId (init 0) == evmChainId
#guard timestamp (init 0) == evmTimestamp
#guard selfLow (init 0) == evmSelf
#guard selfBal (init 0) == evmSelfBalance
#guard callValue (init 0) == evmCallValue
#guard callerW0 (init 0) == evmCallerW0
#guard callerW1 (init 0) == evmCallerW1
#guard callerW2 (init 0) == evmCallerW2
#guard selfW0 (init 0) == evmSelfW0
#guard selfW1 (init 0) == evmSelfW1
#guard selfW2 (init 0) == evmSelfW2
#guard caller20 (init 0) == evmCaller20
#guard self20 (init 0) == evmSelf20

#guard
  match deposit (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match payout (init 0) ⟨1, 2, 3⟩ 4 with
  | .ok (st, ret) => st.dummy == 0 && ret == 4
  | .error _ => false

#guard
  match logTip (init 0) 5 with
  | .ok (st, ret) => st.dummy == 0 && ret == 5
  | .error _ => false

#guard
  match receive (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  let p := ProofForge.Evm.Golden.extractedTipJar
  match ProofForge.Evm.Emit.emitYul p with
  | .error _ => false
  | .ok yul =>
      yul.contains "timestamp()" &&
        yul.contains "chainid()" &&
        yul.contains "callvalue()" &&
        yul.contains "selfbalance()" &&
        yul.contains "if iszero(eq(callvalue()" &&
        yul.contains "call(gas(), mload(0)" &&
        yul.contains "log1(0, 32, 0x" &&
        yul.contains "a20b303e80124ead462817f3d5ce5513d6d36a9ea8085f2cf523499b54a820c3" &&
        yul.contains "        if callvalue() { revert(0, 0) }" &&
        yul.contains "if iszero(calldatasize())" &&
        yul.contains "let pf_recv := callvalue()" &&
        !yul.contains "sol_get_clock_sysvar" &&
        !yul.contains "sol_invoke_signed_c"

#guard
  let p := ProofForge.Evm.Golden.extractedTipJar
  (p.entries.find? (·.ixName == "deposit")).map (·.payable) == some true &&
    (p.entries.find? (·.ixName == "receive")).map (·.payable) == some true &&
    (p.entries.find? (·.ixName == "payout")).map (·.payable) == some false &&
    (p.entries.find? (·.ixName == "logTip")).map (·.payable) == some false &&
    (p.entries.find? (·.ixName == "chainId")).map (·.view) == some true

#guard
  let p := ProofForge.Evm.Golden.extractedTipJar
  let abi := ProofForge.Evm.Emit.emitAbi p
  abi.contains "\"stateMutability\":\"payable\"" &&
    abi.contains "\"name\":\"deposit\"" &&
    abi.contains "\"name\":\"payout\"" &&
    abi.contains "\"type\":\"receive\"" &&
    !abi.contains "\"name\":\"receive\""

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTipJar with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.TipJarSpec
