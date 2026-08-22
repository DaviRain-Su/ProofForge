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
