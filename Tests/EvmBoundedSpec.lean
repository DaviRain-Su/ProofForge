import Examples.EvmBounded
import ProofForge

namespace Tests.EvmBoundedSpec

open Examples.EvmBounded
open ProofForge.Core.Value
open Lean Elab Command

private def short : BoundedVec UInt64 4 :=
  { length := 2, values := #v[11, 13, 0, 0] }

private def full : BoundedVec UInt64 4 :=
  { length := 4, values := #v[11, 13, 17, 19] }

#guard boundedValues (init 0) short == 13
#guard boundedValues (init 0) full == 34

private def left : BoundedVec UInt64 2 :=
  { length := 2, values := #v[11, 13] }

private def right : BoundedVec UInt16 3 :=
  { length := 3, values := #v[17, 19, 23] }

#guard combine (init 0) 7 left true right == 49

private def shortBytes : BoundedBytes 8 :=
  { length := 2, values := #v[11, 13, 0, 0, 0, 0, 0, 0] }

private def fullString : BoundedString 8 :=
  { length := 8, values := #v[97, 98, 99, 100, 101, 102, 103, 104] }

#guard boundedBytes (init 0) shortBytes == 13
#guard boundedString (init 0) fullString == 209

elab "#pf_guard_evm_bounded_abi" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmBounded with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some bounded := program.entries.find? (·.ixName == "boundedValues")
    | throwError "missing boundedValues entry"
  let some combined := program.entries.find? (·.ixName == "combine")
    | throwError "missing combine entry"
  let some bytes := program.entries.find? (·.ixName == "boundedBytes")
    | throwError "missing boundedBytes entry"
  let some text := program.entries.find? (·.ixName == "boundedString")
    | throwError "missing boundedString entry"
  let some echoValues := program.entries.find? (·.ixName == "echoBoundedValues")
    | throwError "missing bounded array result entry"
  let some echoBytes := program.entries.find? (·.ixName == "echoBoundedBytes")
    | throwError "missing bounded bytes result entry"
  let some echoString := program.entries.find? (·.ixName == "echoBoundedString")
    | throwError "missing bounded string result entry"
  let some makeString := program.entries.find? (·.ixName == "makeBoundedString")
    | throwError "missing constructed bounded string result entry"
  unless bounded.logicalParamCount == 1 && bounded.paramCount == 5 &&
      bounded.paramTypes == #[.uint32, .uint64, .uint64, .uint64, .uint64] &&
      bounded.selector == ProofForge.Crypto.Keccak.selector "boundedValues" #["uint64[]"] &&
      bounded.inputPolicy ==
        "0=bounded-array-v1(uint64[];capacity=4;element-words=1)" &&
      combined.logicalParamCount == 4 && combined.paramCount == 9 &&
      combined.paramTypes == #[.uint32, .uint32, .uint64, .uint64, .boolean,
        .uint32, .uint16, .uint16, .uint16] &&
      combined.selector == ProofForge.Crypto.Keccak.selector "combine"
        #["uint32", "uint64[]", "bool", "uint16[]"] &&
      combined.inputPolicy ==
        "1=bounded-array-v1(uint64[];capacity=2;element-words=1)," ++
        "3=bounded-array-v1(uint16[];capacity=3;element-words=1)" &&
      bytes.logicalParamCount == 1 && bytes.paramCount == 9 &&
      bytes.paramTypes == #[.uint32, .uint8, .uint8, .uint8, .uint8,
        .uint8, .uint8, .uint8, .uint8] &&
      bytes.selector == ProofForge.Crypto.Keccak.selector "boundedBytes" #["bytes"] &&
      bytes.inputPolicy == "0=packed-bytes-v1(bytes;capacity=8;utf8=false)" &&
      text.logicalParamCount == 1 && text.paramCount == 9 &&
      text.paramTypes == bytes.paramTypes &&
      text.selector == ProofForge.Crypto.Keccak.selector "boundedString" #["string"] &&
      text.inputPolicy == "0=packed-bytes-v1(string;capacity=8;utf8=true)" &&
      echoValues.paramCount == 5 && echoValues.retCount == 5 &&
      echoValues.retTypes == #[.uint32, .uint16, .uint16, .uint16, .uint16] &&
      echoValues.outputPlan == some (.boundedArray {
        capacity := 4, elementTypeName := "uint16", elementWords := #[.uint16]
      }) &&
      echoValues.outputPolicy == "bounded-array-return-v1(uint16[];capacity=4;element-words=1)" &&
      echoBytes.retCount == 9 && echoBytes.outputPlan == some (.packedBytes {
        capacity := 8, validateUtf8 := false }) &&
      echoString.retCount == 9 && echoString.outputPlan == some (.packedBytes {
        capacity := 8, validateUtf8 := true }) &&
      makeString.paramCount == 9 && makeString.outputPlan == echoString.outputPlan do
    throwError s!"wrong EVM bounded ABI methods: {repr bounded}, {repr combined}, " ++
      s!"{repr bytes}, {repr text}"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless yul.contains "if lt(calldatasize(), 36)" &&
      yul.contains "if iszero(eq(calldataload(4), abi_tail))" &&
      yul.contains "if gt(arg0, 4)" && yul.contains "let arg4 := 0" &&
      yul.contains "if iszero(eq(abi_size, abi_tail))" &&
      yul.contains "if lt(calldatasize(), 132)" &&
      yul.contains "if iszero(eq(calldataload(36), abi_tail))" &&
      yul.contains "if iszero(eq(calldataload(100), abi_tail))" &&
      yul.contains "if gt(arg8, 0xffff)" &&
      yul.contains "let abi_padded0 := and(add(arg0, 31), not(31))" &&
      yul.contains "for { let abi_padding_i0 := arg0 }" &&
      yul.contains "arg8 := byte(0, calldataload" &&
      yul.contains "let abi_utf8_need0 := 0" &&
      yul.contains "if abi_utf8_need0 { revert(0, 0) }" &&
      yul.contains "mstore(0, 32)" && yul.contains "mstore(32, arg0)" &&
      yul.contains "return(0, add(64, mul(arg0, 32)))" &&
      yul.contains "mstore8(71," && yul.contains "let abi_ret_padded := and(add(arg0, 31)" &&
      yul.contains "let abi_ret_utf8_need0 := 0" &&
      yul.contains "if abi_ret_utf8_need0 { revert(0, 0) }" &&
      abi.contains "\"name\":\"arg0\",\"type\":\"uint64[]\"" &&
      abi.contains "\"name\":\"arg1\",\"type\":\"uint64[]\"" &&
      abi.contains "\"name\":\"arg3\",\"type\":\"uint16[]\"" &&
      abi.contains "\"name\":\"arg0\",\"type\":\"bytes\"" &&
      abi.contains "\"name\":\"arg0\",\"type\":\"string\"" &&
      abi.contains "\"name\":\"echoBoundedValues\"" &&
      abi.contains "\"outputs\":[{\"name\":\"\",\"type\":\"uint16[]\"}]" &&
      abi.contains "\"name\":\"echoBoundedBytes\"" &&
      abi.contains "\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}]" &&
      abi.contains "\"name\":\"echoBoundedString\"" &&
      abi.contains "\"outputs\":[{\"name\":\"\",\"type\":\"string\"}]" do
    throwError "bounded ABI offsets, bounds, zero frame, padding guards, or JSON are incomplete"
  let ctorSchema : ProofForge.Core.Codec.Schema := .boundedArray 2 (.scalar .uint64)
  let ctorPlan ←
    match ProofForge.Evm.Codec.inputPlan ctorSchema with
    | .ok plan => pure plan
    | .error reason => throwError reason
  let dynamicCtor := {
    program with
    constructor := {
      program.constructor with
      paramCount := ctorPlan.wordCount
      paramWidths := #[]
      paramTypes := ctorPlan.words
      paramSchemas := #[ctorSchema]
      inputPolicy := ProofForge.Evm.IR.inputPolicyOf #[ctorPlan]
    }
  }
  unless (match ProofForge.Evm.Emit.emitYul dynamicCtor with
      | .error reason => reason.contains "dynamic constructor inputs are not supported"
      | .ok _ => false) &&
      (match ProofForge.Evm.Emit.emitAbiChecked dynamicCtor with
      | .error reason => reason.contains "dynamic constructor inputs are not supported"
      | .ok _ => false) do
    throwError "bounded dynamic constructor input did not fail closed"

#pf_guard_evm_bounded_abi

#guard
  match ProofForge.Evm.Codec.inputPlan
      (ProofForge.Core.Codec.Schema.boundedArray 2
        (ProofForge.Core.Codec.Schema.boundedArray 2
          (ProofForge.Core.Codec.Schema.scalar .uint64))) with
  | .error _ => true
  | .ok _ => false

#guard
  match ProofForge.Evm.Codec.inputPlan (.boundedArray 64 (.scalar .uint64)) with
  | .error reason => reason.contains "local frame exceeds 64 words"
  | .ok _ => false

#guard
  match ProofForge.Evm.Codec.inputPlan (.boundedBytes 64) with
  | .error reason => reason.contains "packed bytes local frame exceeds 64 words"
  | .ok _ => false

#guard
  match ProofForge.Evm.Codec.dynamicOutputPlan
      (.boundedArray 2 (.boundedArray 2 (.scalar .uint64))) with
  | .error _ => true
  | .ok _ => false

#guard
  match ProofForge.Evm.Codec.dynamicOutputPlan (.boundedString 64) with
  | .error reason => reason.contains "result frame exceeds 64 words"
  | .ok _ => false

end Tests.EvmBoundedSpec
