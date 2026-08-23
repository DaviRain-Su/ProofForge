import Examples.EvmCtx
import ProofForge

namespace Tests.EvmCtxSpec

open Examples.EvmCtx
open ProofForge.Evm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard caller (init 0) == evmCaller
#guard height (init 0) == evmBlockNumber

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedEvmCtx with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "and(caller(), 0xffffffffffffffff)" &&
            yul.contains "let v0 := number()" &&
            yul.contains "if gt(v0, 0xffffffffffffffff)" &&
            !yul.contains "sol_get_clock_sysvar" &&
            !yul.contains "ACC0_KEY"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.EvmCtxSpec
