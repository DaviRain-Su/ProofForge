import Examples.EvmCtx
import SolanaLean

namespace Tests.EvmCtxSpec

open Examples.EvmCtx
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard caller (init 0) == evmCaller
#guard height (init 0) == evmBlockNumber

#guard
  match SolanaLean.Evm.IR.fromProgram SolanaLean.Golden.extractedEvmCtx with
  | .error _ => false
  | .ok p =>
      match SolanaLean.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "and(caller(), 0xffffffffffffffff)" &&
            yul.contains "let v0 := number()" &&
            yul.contains "if gt(v0, 0xffffffffffffffff)" &&
            !yul.contains "sol_get_clock_sysvar" &&
            !yul.contains "ACC0_KEY"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.EvmCtxSpec
