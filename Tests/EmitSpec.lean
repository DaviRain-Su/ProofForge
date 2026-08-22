import SolanaLean

#solana_extract SolanaLean.Counter.init SolanaLean.Counter.increment SolanaLean.Counter.get

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.counterProgram with
  | .error _ => false
  | .ok asm =>
      asm.contains "entrypoint:" &&
      asm.contains "body_increment:" &&
      asm.contains SolanaLean.Emit.overflowCode &&
      asm.contains SolanaLean.Emit.layoutMarker &&
      asm.contains SolanaLean.Emit.discInit &&
      asm.contains "call sol_set_return_data"

#guard
  match SolanaLean.Emit.emitCounterAsm { name := "x", methods := #[] } with
  | .error "extract/unsupported: not counter shape" => true
  | _ => false
