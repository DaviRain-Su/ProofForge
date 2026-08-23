import ProofForge
import Examples.Counter

#pf_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.get

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Extract.Legacy.counterProgram with
  | .error "extract/unsupported: init missing returnState" => true
  | .error "extract/unsupported: increment missing checked arith" => true
  | _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm { name := "x", methods := #[] } with
  | .error "extract/unsupported: not program shape" => true
  | _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      let inc :=
        match asm.splitOn "body_increment:" with
        | _ :: rest :: _ => rest
        | _ => ""
      match inc.splitOn "ACC0_DATA + 8" with
      | _ :: after :: _ => after.contains "INSTRUCTION_DATA + 8"
      | _ => false

#guard
  match ProofForge.Svm.ABI.fieldOffset ProofForge.Golden.extractedCounter "value" with
  | some 8 => true
  | _ => false

private def pairShape : ProofForge.Extract.Legacy.Program :=
  { name := "Pair"
    slots := #[{ name := "left" }, { name := "right" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "creditLeft", ixName := "creditLeft", paramCount := 1
        ops := #[
          .checkedAddU64 (.field (.arg 1) "left") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "getLeft", ixName := "getLeft", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "left")] }
    ] }

#guard
  match ProofForge.Svm.ABI.fieldOffset pairShape "right" with
  | some 16 => true
  | _ => false

#guard ProofForge.Svm.ABI.layoutSig pairShape == "2|0:left:0:8:8:u64-le|1:right:0:16:8:u64-le"

#guard
  match ProofForge.Svm.ABI.layoutMarkerHex pairShape with
  | .ok "0x20d45b635e2b016f" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.layoutMarkerHex ProofForge.Golden.extractedCounter with
  | .ok "0xbbe897f0336e6fc" => true
  | _ => false

#guard
  let l := ProofForge.Svm.ABI.inputLayout ProofForge.Golden.extractedCounter
  l.rentEpoch == 0x2870 && l.instructionDataLen == 0x2878 && l.instructionData == 0x2880

#guard
  let l := ProofForge.Svm.ABI.inputLayout ProofForge.Golden.extractedPair
  l.rentEpoch == 0x2878 && l.instructionDataLen == 0x2880 && l.instructionData == 0x2888

#guard
  match ProofForge.Svm.Emit.emitCounterAsm pairShape with
  | .error _ => false
  | .ok asm =>
      asm.contains "ACC0_DATA + 8" &&
        asm.contains "ACC0_DATA + 16" &&
        asm.contains "jne r1, 24," &&
        asm.contains "0x20d45b635e2b016f" &&
        asm.contains ".equ INSTRUCTION_DATA, 10376"

#guard
  match ProofForge.Svm.ABI.layoutMarkerHex
      { name := "X", slots := #[{ name := "a" }, { name := "b" }, { name := "c" }], methods := #[] } with
  | .ok "0xa2e4c31e74585ac3" => true
  | _ => false

private def swappedIncrement : ProofForge.Extract.Legacy.Program :=
  { name := "Counter"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "increment", ixName := "increment", paramCount := 1
        ops := #[
          .checkedAddU64 (.arg 0) (.field (.arg 1) "value"),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "value")] }
    ] }

#guard
  match ProofForge.Svm.Emit.emitCounterAsm swappedIncrement with
  | .error _ => false
  | .ok asm =>
      let inc :=
        match asm.splitOn "body_increment:" with
        | _ :: rest :: _ => rest
        | _ => ""
      match inc.splitOn "INSTRUCTION_DATA + 8" with
      | _ :: after :: _ => after.contains "ACC0_DATA + 8"
      | _ => false
