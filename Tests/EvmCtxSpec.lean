import Examples.Evm.EvmCtx
import ProofForge

namespace Tests.EvmCtxSpec

open Examples.Evm.EvmCtx
open ProofForge.Evm.Sdk
open Lean Elab Command

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard caller (init 0) == Context.callerLow
#guard height (init 0) == Context.blockNumber
#guard gasLeft (init 0) == Context.gasLeft
#guard gasPrice (init 0) == Context.gasPrice
#guard blobBaseFee (init 0) == Context.blobBaseFee
#guard blobHash (init 0) 3 == Context.blobHash 3
#guard origin (init 0) == Context.origin
#guard selector (init 0) == Context.selector
#guard calldataSize (init 0) == Context.calldataSize
#guard blockHash (init 0) 37 == Context.blockHash 37
#guard codeSize (init 0) ⟨1, 2, 3⟩ == Address.codeSize ⟨1, 2, 3⟩
#guard hasCode (init 0) ⟨1, 2, 3⟩ == Address.hasCode ⟨1, 2, 3⟩
#guard codeHash (init 0) ⟨1, 2, 3⟩ == Address.codeHash ⟨1, 2, 3⟩
#guard balance (init 0) ⟨1, 2, 3⟩ == Address.balance ⟨1, 2, 3⟩

#guard aggregate (init 0) ⟨11, ⟨3, true⟩⟩ (13, 17) #v[19, 23, 29] == (93, true)
#guard optionValue (init 0) none == 5
#guard optionValue (init 0) (some 37) == 38
#guard taggedValue (init 0) .idle == 3
#guard taggedValue (init 0) (.one 7) == 17
#guard taggedValue (init 0) (.pair 11 29) == 40
#guard echoOptionValue (init 0) none == none
#guard echoOptionValue (init 0) (some 37) == some 37
#guard match echoTaggedValue (init 0) (.pair 11 29) with
  | .pair 11 29 => true
  | _ => false

elab "#pf_guard_evm_aggregate_abi" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Evm.EvmCtx with
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
  let some optionMethod := program.entries.find? (·.ixName == "optionValue")
    | throwError "missing EVM Option entry"
  let some taggedMethod := program.entries.find? (·.ixName == "taggedValue")
    | throwError "missing EVM payload-enum entry"
  let some echoOption := program.entries.find? (·.ixName == "echoOptionValue")
    | throwError "missing EVM tagged Option result entry"
  let some echoTagged := program.entries.find? (·.ixName == "echoTaggedValue")
    | throwError "missing EVM tagged enum result entry"
  let some gasMethod := program.entries.find? (·.ixName == "gasLeft")
    | throwError "missing EVM gas-left entry"
  unless optionMethod.logicalParamCount == 1 && optionMethod.paramCount == 2 &&
      optionMethod.paramTypes == #[.boolean, .uint64] &&
      optionMethod.selector == ProofForge.Crypto.Keccak.selector "optionValue"
        #["(bool,uint64)"] &&
      optionMethod.inputPolicy ==
        "0=tagged-tuple-v1((bool,uint64);0:1:1:[0,1])" &&
      taggedMethod.logicalParamCount == 1 && taggedMethod.paramCount == 3 &&
      taggedMethod.paramTypes == #[.uint8, .uint64, .uint64] &&
      taggedMethod.selector == ProofForge.Crypto.Keccak.selector "taggedValue"
        #["(uint8,uint64,uint64)"] &&
      taggedMethod.inputPolicy ==
        "0=tagged-tuple-v1((uint8,uint64,uint64);0:1:2:[0,1,2])" &&
      echoOption.retTypes == #[.boolean, .uint64] &&
      echoOption.outputPlan == some (.taggedTuple {
        typeName := "(bool,uint64)", words := #[.boolean, .uint64],
        activePayloadWords := #[0, 1]
      }) &&
      echoOption.outputPolicy == "tagged-tuple-return-v1((bool,uint64);active=[0,1])" &&
      echoTagged.retTypes == #[.uint8, .uint64, .uint64] &&
      echoTagged.outputPlan == some (.taggedTuple {
        typeName := "(uint8,uint64,uint64)", words := #[.uint8, .uint64, .uint64],
        activePayloadWords := #[0, 1, 2]
      }) &&
      echoTagged.outputPolicy ==
        "tagged-tuple-return-v1((uint8,uint64,uint64);active=[0,1,2])" &&
      gasMethod.retTypes == #[.uint256] && gasMethod.retCount == 4 do
    throwError s!"wrong EVM Tagged Tuple v1/environment methods: {repr optionMethod}, {repr taggedMethod}, {repr gasMethod}"
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
      yul.contains "if iszero(eq(calldatasize(), 68))" &&
      yul.contains "if and(eq(arg0, 0), arg1)" &&
      yul.contains "if iszero(eq(calldatasize(), 100))" &&
      yul.contains "if iszero(lt(arg0, 3))" &&
      yul.contains "if and(eq(arg0, 1), arg2)" &&
      yul.contains "let abi_ret_tag := arg0" &&
      yul.contains "if and(eq(abi_ret_tag, 0), abi_ret_p0)" &&
      yul.contains "if and(eq(abi_ret_tag, 1), abi_ret_p1)" &&
      yul.contains " := gas()" &&
      yul.contains "return(0, 96)" &&
      yul.contains "return(0, 64)" &&
      abi.contains "\"type\":\"tuple\",\"components\":[{\"name\":\"amount\"" &&
      abi.contains "\"name\":\"details\",\"type\":\"tuple\"" &&
      abi.contains "\"name\":\"arg2\",\"type\":\"uint16[3]\"" &&
      abi.contains "\"name\":\"present\",\"type\":\"bool\"" &&
      abi.contains "\"name\":\"tag\",\"type\":\"uint8\"" &&
      abi.contains "\"name\":\"p1\",\"type\":\"uint64\"" &&
      abi.contains "\"name\":\"echoOptionValue\"" &&
      abi.contains "\"name\":\"echoTaggedValue\"" &&
      abi.contains "\"name\":\"gasLeft\"" &&
      abi.contains "\"outputs\":[{\"name\":\"\",\"type\":\"tuple\"" do
    throwError "EVM aggregate/tagged calldata guards, return packing, or ABI JSON are incomplete"

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

#guard
  match ProofForge.Evm.Codec.outputPlan
      (.option (.tuple #[.scalar .uint64, .scalar .uint64])) with
  | .error reason => reason.contains "one-limb scalar payload"
  | .ok _ => false

#guard
  match ProofForge.Evm.Codec.outputPlan (.enumeration "Bad" 8 #[
      ("bad", .scalar .uint32)]) with
  | .error reason => reason.contains "must be UInt64"
  | .ok _ => false

end Tests.EvmCtxSpec
