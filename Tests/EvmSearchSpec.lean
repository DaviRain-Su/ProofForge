import Examples.Evm.EvmSearch
import Examples.Evm.EvmFindIndex
import ProofForge

namespace Tests.EvmSearchSpec

open Examples.Evm.EvmSearch
open ProofForge.Core.Value
open Lean Elab Command

private def bytes : BoundedBytes 3 :=
  { length := 3, values := #v[0x61, 0x62, 0x63] }

private def suffix : BoundedBytes 2 :=
  { length := 2, values := #v[0x62, 0x63] }

private def absent : BoundedBytes 2 :=
  { length := 2, values := #v[0x61, 0x63] }

private def euro : BoundedString 3 :=
  { length := 3, values := #v[0xe2, 0x82, 0xac] }

private def empty : BoundedString 1 :=
  { length := 0, values := #v[0xff] }

#guard bytes.contains suffix
#guard !bytes.contains absent
#guard euro.contains euro
#guard euro.contains empty

elab "#pf_guard_evm_search" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Evm.EvmSearch with
    | .ok source => pure source
    | .error reason => throwError reason
  let findSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.Evm.EvmFindIndex with
    | .ok source => pure source
    | .error reason => throwError reason
  let some sourceBytes := source.methods.find? (·.ixName == "bytesContains")
    | throwError "missing source bytes substring method"
  let some sourceStrings := source.methods.find? (·.ixName == "stringsContains")
    | throwError "missing source string substring method"
  let some sourceBytesFind := findSource.methods.find? (·.ixName == "bytesFindIndex")
    | throwError "missing source bytes first-position method"
  let some sourceStringsFind := findSource.methods.find? (·.ixName == "stringsFindIndex")
    | throwError "missing source string first-position method"
  let some sourceBytesStarts := source.methods.find? (·.ixName == "bytesStartsWith")
    | throwError "missing source bytes prefix method"
  let some sourceStringsStarts := source.methods.find? (·.ixName == "stringsStartsWith")
    | throwError "missing source string prefix method"
  let some sourceBytesEnds := source.methods.find? (·.ixName == "bytesEndsWith")
    | throwError "missing source bytes suffix method"
  let some sourceStringsEnds := source.methods.find? (·.ixName == "stringsEndsWith")
    | throwError "missing source string suffix method"
  for method in #[sourceBytes, sourceBytesStarts, sourceBytesEnds] do
    unless method.paramSchemas == #[.boundedBytes 3, .boundedBytes 3] &&
        method.retSchema == .scalar .boolean do
      throwError s!"{method.ixName} lost its bounded bytes schema"
  for method in #[sourceStrings, sourceStringsStarts, sourceStringsEnds] do
    unless method.paramSchemas == #[.boundedString 3, .boundedString 3] &&
        method.retSchema == .scalar .boolean do
      throwError s!"{method.ixName} lost its bounded string schema"
  unless sourceBytesFind.paramSchemas == #[.boundedBytes 3, .boundedBytes 3] &&
      sourceBytesFind.retSchema == .option (.scalar .uint64) && sourceBytesFind.retCount == 2 &&
      sourceStringsFind.paramSchemas == #[.boundedString 3, .boundedString 3] &&
      sourceStringsFind.retSchema == .option (.scalar .uint64) &&
      sourceStringsFind.retCount == 2 do
    throwError "typed first-position methods lost their fixed Option frame"
  let rec loopBounds (fuel : Nat) (ops : Array ProofForge.Extract.Ops.Op) : Array Nat :=
    match fuel with
    | 0 => #[]
    | fuel' + 1 => ops.foldl (init := #[]) fun bounds op =>
        match op with
        | .forBody bound body => bounds.push bound ++ loopBounds fuel' body
        | .ite _ _ _ yes no => bounds ++ loopBounds fuel' yes ++ loopBounds fuel' no
        | _ => bounds
  for method in #[sourceBytes, sourceStrings, sourceBytesStarts, sourceStringsStarts,
      sourceBytesEnds, sourceStringsEnds, sourceBytesFind, sourceStringsFind] do
    unless loopBounds 8 method.ops == #[9] do
      throwError s!"{method.ixName} lost the shared static product scan"
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let findProgram ←
    match ProofForge.Evm.IR.fromExtracted findSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let some bytesMethod := program.entries.find? (·.ixName == "bytesContains")
    | throwError "missing EVM bytes substring method"
  let some stringsMethod := program.entries.find? (·.ixName == "stringsContains")
    | throwError "missing EVM string substring method"
  let some bytesFind := findProgram.entries.find? (·.ixName == "bytesFindIndex")
    | throwError "missing EVM bytes first-position method"
  let some stringsFind := findProgram.entries.find? (·.ixName == "stringsFindIndex")
    | throwError "missing EVM string first-position method"
  let some bytesStarts := program.entries.find? (·.ixName == "bytesStartsWith")
    | throwError "missing EVM bytes prefix method"
  let some stringsStarts := program.entries.find? (·.ixName == "stringsStartsWith")
    | throwError "missing EVM string prefix method"
  let some bytesEnds := program.entries.find? (·.ixName == "bytesEndsWith")
    | throwError "missing EVM bytes suffix method"
  let some stringsEnds := program.entries.find? (·.ixName == "stringsEndsWith")
    | throwError "missing EVM string suffix method"
  let bytesPolicy :=
    "0=packed-bytes-v1(bytes;capacity=3;utf8=false)," ++
    "1=packed-bytes-v1(bytes;capacity=3;utf8=false)"
  let stringsPolicy :=
    "0=packed-bytes-v1(string;capacity=3;utf8=true)," ++
    "1=packed-bytes-v1(string;capacity=3;utf8=true)"
  for (method, name) in #[(bytesMethod, "bytesContains"), (bytesStarts, "bytesStartsWith"),
      (bytesEnds, "bytesEndsWith")] do
    unless method.logicalParamCount == 2 && method.paramCount == 8 &&
        method.selector == ProofForge.Crypto.Keccak.selector name #["bytes", "bytes"] &&
        method.inputPolicy == bytesPolicy do
      throwError s!"{name} ABI lost an independent canonical dynamic tail"
  for (method, name) in #[(stringsMethod, "stringsContains"),
      (stringsStarts, "stringsStartsWith"), (stringsEnds, "stringsEndsWith")] do
    unless method.logicalParamCount == 2 && method.paramCount == 8 &&
        method.selector == ProofForge.Crypto.Keccak.selector name #["string", "string"] &&
        method.inputPolicy == stringsPolicy do
      throwError s!"{name} ABI lost an independent canonical dynamic tail"
  let optionPlan : ProofForge.Evm.Codec.OutputPlan := .taggedTuple {
    typeName := "(bool,uint64)"
    words := #[.boolean, .uint64]
    activePayloadWords := #[0, 1]
  }
  for (method, name, policy) in #[(bytesFind, "bytesFindIndex", bytesPolicy),
      (stringsFind, "stringsFindIndex", stringsPolicy)] do
    unless method.logicalParamCount == 2 && method.paramCount == 8 &&
        method.selector == ProofForge.Crypto.Keccak.selector name
          (if name == "bytesFindIndex" then #["bytes", "bytes"] else #["string", "string"]) &&
        method.inputPolicy == policy && method.retTypes == #[.boolean, .uint64] &&
        method.outputPlan == some optionPlan &&
        method.outputPolicy == "tagged-tuple-return-v1((bool,uint64);active=[0,1])" do
      throwError s!"{name} lost its canonical Option result binding"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let findYul ←
    match ProofForge.Evm.Emit.emitYul findProgram with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  let findAbi ←
    match ProofForge.Evm.Emit.emitAbiChecked findProgram with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless yul.contains "mstore(64, memoryguard(4096))" &&
      findYul.contains "mstore(64, memoryguard(4096))" &&
      abi.contains "\"name\":\"bytesContains\"" &&
      abi.contains "\"name\":\"stringsContains\"" &&
      findAbi.contains "\"name\":\"bytesFindIndex\"" &&
      findAbi.contains "\"name\":\"stringsFindIndex\"" &&
      abi.contains "\"name\":\"bytesStartsWith\"" &&
      abi.contains "\"name\":\"stringsStartsWith\"" &&
      abi.contains "\"name\":\"bytesEndsWith\"" &&
      abi.contains "\"name\":\"stringsEndsWith\"" do
    throwError "bounded search methods did not reach EVM Yul/ABI emission"

#pf_guard_evm_search

end Tests.EvmSearchSpec
