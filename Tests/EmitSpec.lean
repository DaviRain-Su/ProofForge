import SolanaLean
import Examples.Counter

#solana_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.get

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.counterProgram with
  | .error "extract/unsupported: init missing returnState" => true
  | .error "extract/unsupported: increment missing checked arith" => true
  | _ => false

#guard
  match SolanaLean.Emit.emitCounterAsm { name := "x", methods := #[] } with
  | .error "extract/unsupported: not counter shape" => true
  | _ => false

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.extractedCounter with
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
  match SolanaLean.IR.fieldOffset SolanaLean.IR.extractedCounter "value" with
  | some 8 => true
  | _ => false

private def pairShape : SolanaLean.IR.Program :=
  { name := "Pair"
    fields := #["left", "right"]
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
  match SolanaLean.IR.fieldOffset pairShape "right" with
  | some 16 => true
  | _ => false

#guard SolanaLean.IR.layoutSig pairShape == "2|0:left:0:8:8:u64-le|1:right:0:16:8:u64-le"

#guard
  match SolanaLean.IR.layoutMarkerHex pairShape with
  | .ok "0x20d45b635e2b016f" => true
  | _ => false

#guard
  match SolanaLean.IR.layoutMarkerHex SolanaLean.IR.extractedCounter with
  | .ok "0xbbe897f0336e6fc" => true
  | _ => false

#guard
  let l := SolanaLean.IR.inputLayout SolanaLean.IR.extractedCounter
  l.rentEpoch == 0x2870 && l.instructionDataLen == 0x2878 && l.instructionData == 0x2880

#guard
  let l := SolanaLean.IR.inputLayout SolanaLean.IR.extractedPair
  l.rentEpoch == 0x2878 && l.instructionDataLen == 0x2880 && l.instructionData == 0x2888

#guard
  match SolanaLean.Emit.emitCounterAsm pairShape with
  | .error _ => false
  | .ok asm =>
      asm.contains "ACC0_DATA + 8" &&
        asm.contains "ACC0_DATA + 16" &&
        asm.contains "jne r1, 24," &&
        asm.contains "0x20d45b635e2b016f" &&
        asm.contains ".equ INSTRUCTION_DATA, 10376"

#guard
  match SolanaLean.IR.layoutMarkerHex
      { name := "X", fields := #["a", "b", "c"], methods := #[] } with
  | .error reason => reason.startsWith "extract/unsupported: unregistered layout"
  | .ok _ => false

private def swappedIncrement : SolanaLean.IR.Program :=
  { name := "Counter"
    fields := #["value"]
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
  match SolanaLean.Emit.emitCounterAsm swappedIncrement with
  | .error _ => false
  | .ok asm =>
      let inc :=
        match asm.splitOn "body_increment:" with
        | _ :: rest :: _ => rest
        | _ => ""
      match inc.splitOn "INSTRUCTION_DATA + 8" with
      | _ :: after :: _ => after.contains "ACC0_DATA + 8"
      | _ => false
