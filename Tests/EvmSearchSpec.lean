import Examples.EvmSearch
import ProofForge

namespace Tests.EvmSearchSpec

open Examples.EvmSearch
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
    match ProofForge.Extract.extractModuleIR env `Examples.EvmSearch with
    | .ok source => pure source
    | .error reason => throwError reason
  let some sourceBytes := source.methods.find? (·.ixName == "bytesContains")
    | throwError "missing source bytes substring method"
  let some sourceStrings := source.methods.find? (·.ixName == "stringsContains")
    | throwError "missing source string substring method"
  unless sourceBytes.paramSchemas == #[.boundedBytes 3, .boundedBytes 3] &&
      sourceStrings.paramSchemas == #[.boundedString 3, .boundedString 3] &&
      sourceBytes.retSchema == .scalar .boolean && sourceStrings.retSchema == .scalar .boolean do
    throwError "substring source methods lost their bounded logical schemas"
  let rec loopBounds (fuel : Nat) (ops : Array ProofForge.Extract.Ops.Op) : Array Nat :=
    match fuel with
    | 0 => #[]
    | fuel' + 1 => ops.foldl (init := #[]) fun bounds op =>
        match op with
        | .forBody bound body => bounds.push bound ++ loopBounds fuel' body
        | .ite _ _ _ yes no => bounds ++ loopBounds fuel' yes ++ loopBounds fuel' no
        | _ => bounds
  unless loopBounds 8 sourceBytes.ops == #[9] && loopBounds 8 sourceStrings.ops == #[9] do
    throwError "static product substring loop was not preserved exactly"
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some bytesMethod := program.entries.find? (·.ixName == "bytesContains")
    | throwError "missing EVM bytes substring method"
  let some stringsMethod := program.entries.find? (·.ixName == "stringsContains")
    | throwError "missing EVM string substring method"
  unless bytesMethod.logicalParamCount == 2 && bytesMethod.paramCount == 8 &&
      bytesMethod.selector ==
        ProofForge.Crypto.Keccak.selector "bytesContains" #["bytes", "bytes"] &&
      bytesMethod.inputPolicy ==
        "0=packed-bytes-v1(bytes;capacity=3;utf8=false)," ++
        "1=packed-bytes-v1(bytes;capacity=3;utf8=false)" &&
      stringsMethod.logicalParamCount == 2 && stringsMethod.paramCount == 8 &&
      stringsMethod.selector ==
        ProofForge.Crypto.Keccak.selector "stringsContains" #["string", "string"] &&
      stringsMethod.inputPolicy ==
        "0=packed-bytes-v1(string;capacity=3;utf8=true)," ++
        "1=packed-bytes-v1(string;capacity=3;utf8=true)" do
    throwError "substring ABI lost an independent canonical dynamic tail"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless !yul.isEmpty && abi.contains "\"name\":\"bytesContains\"" &&
      abi.contains "\"name\":\"stringsContains\"" do
    throwError "substring methods did not reach EVM Yul/ABI emission"

#pf_guard_evm_search

end Tests.EvmSearchSpec
