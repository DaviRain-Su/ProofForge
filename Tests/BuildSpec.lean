import SolanaLean
import Examples.Counter
import Examples.Pair

#solana_build Examples.Counter

#solana_build Examples.Pair

/--
error: extract/unsupported: no solana_entry
-/
#guard_msgs (error) in
#solana_build Tests.Fixtures

#guard
  match SolanaLean.IR.discHexOf "decrement" 1 with
  | .ok "0x1b92f24dfb29d300" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "creditLeft" 1 with
  | .ok "0xca5ea3052ea3b57e" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "getLeft" 0 with
  | .ok "0xe391a39d1496f393" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "scale" 1 with
  | .ok "0x5f760731ac44bf15" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "nonzero" 0 with
  | .ok "0x9d4170637dda8281" => true
  | _ => false

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains "0x1b92f24dfb29d300" &&
        asm.contains "call decrement" &&
        asm.contains "call increment"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.extractedPair with
  | .error _ => false
  | .ok asm =>
      asm.contains "0xca5ea3052ea3b57e" &&
        asm.contains "call creditLeft" &&
        asm.contains "call getLeft" &&
        !asm.contains "call increment"
