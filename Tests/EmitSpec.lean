import SolanaLean

#solana_extract SolanaLean.Counter.init SolanaLean.Counter.increment SolanaLean.Counter.get

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.counterProgram with
  | .error "extract/unsupported: init missing returnState" => true
  | .error "extract/unsupported: increment missing checkedAddU64" => true
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

private def swappedIncrement : SolanaLean.IR.Program :=
  { name := "Counter"
    methods := #[
      { kind := .init, name := "init"
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "increment"
        ops := #[
          .checkedAddU64 (.arg 0) (.field (.arg 1) "value"),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "get"
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
