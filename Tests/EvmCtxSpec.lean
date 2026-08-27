import Examples.EvmCtx
import ProofForge

namespace Tests.EvmCtxSpec

open Examples.EvmCtx
open ProofForge.Evm.Runtime
open Lean Elab Command

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard caller (init 0) == evmCaller
#guard height (init 0) == evmBlockNumber

#guard aggregate (init 0) ⟨11, ⟨3, true⟩⟩ (13, 17) #v[19, 23, 29] == (93, true)

elab "#pf_guard_evm_aggregate_abi" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmCtx with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some method := program.entries.find? (·.ixName == "aggregate")
    | throwError "missing EVM aggregate entry"
  let signature := #["(uint64,(uint8,bool))", "(uint32,uint64)", "uint16[3]"]
  unless method.logicalParamCount == 3 && method.paramCount == 8 &&
      method.paramTypes == #[.uint64, .uint8, .boolean, .uint32, .uint64,
        .uint16, .uint16, .uint16] &&
      method.selector == ProofForge.Crypto.Keccak.selector "aggregate" signature &&
      method.retTypes == #[.uint64, .boolean] do
    throwError s!"wrong EVM aggregate method: {repr method}"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless yul.contains "if iszero(eq(calldatasize(), 260))" &&
      yul.contains "if gt(arg2, 1)" && yul.contains "if gt(arg7, 0xffff)" &&
      yul.contains "return(0, 64)" &&
      abi.contains "\"type\":\"tuple\",\"components\":[{\"name\":\"amount\"" &&
      abi.contains "\"name\":\"details\",\"type\":\"tuple\"" &&
      abi.contains "\"name\":\"arg2\",\"type\":\"uint16[3]\"" &&
      abi.contains "\"outputs\":[{\"name\":\"\",\"type\":\"tuple\"" do
    throwError "EVM aggregate calldata guards, return packing, or ABI JSON are incomplete"

#pf_guard_evm_aggregate_abi

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
