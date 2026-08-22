import SolanaLean
import Examples.Counter
import Examples.Pair
import Examples.Flag
import Examples.Maybe
import Examples.Window
import Examples.Phase
import Examples.Choice
import Examples.Clock
import Examples.Transfer
import Examples.Ping
import Examples.Call
import Examples.Info
import Examples.Pda
import Examples.Signed
import Examples.Create
import Examples.TokenXfer
import Examples.Ata
import Examples.Rent
import Examples.TokenMint
import Examples.SysAlloc
import Examples.TokenAcc
import Examples.Memo
import Examples.CreatePda
import Examples.TokenApprove
import Examples.TokenFreeze
import Examples.TokenAuth
import Examples.Epoch
import Examples.TokenSize
import Examples.SysSeed

#solana_build Examples.Counter

#solana_build Examples.Pair

#solana_build Examples.Flag

#solana_build Examples.Maybe

#solana_build Examples.Window

#solana_build Examples.Phase

#solana_build Examples.Choice

#solana_build Examples.Clock

#solana_build Examples.Transfer

#solana_build Examples.Ping

#solana_build Examples.Call

#solana_build Examples.Info

#solana_build Examples.Pda

#solana_build Examples.Signed

#solana_build Examples.Create

#solana_build Examples.TokenXfer

#solana_build Examples.Ata

#solana_build Examples.Rent

#solana_build Examples.TokenMint

#solana_build Examples.SysAlloc

#solana_build Examples.TokenAcc

#solana_build Examples.Memo

#solana_build Examples.CreatePda

#solana_build Examples.TokenApprove

#solana_build Examples.TokenFreeze

#solana_build Examples.TokenAuth

#solana_build Examples.Epoch

#solana_build Examples.TokenSize

#solana_build Examples.SysSeed

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
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains "0x1b92f24dfb29d300" &&
        asm.contains "call decrement" &&
        asm.contains "call increment"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedPair with
  | .error _ => false
  | .ok asm =>
      asm.contains "0xca5ea3052ea3b57e" &&
        asm.contains "call creditLeft" &&
        asm.contains "call getLeft" &&
        !asm.contains "call increment"

#guard
  SolanaLean.IR.digestHex SolanaLean.Golden.extractedCounter ==
    SolanaLean.IR.digestHex SolanaLean.Golden.extractedCounter

#guard
  SolanaLean.IR.digestHex SolanaLean.Golden.extractedCounter !=
    SolanaLean.IR.digestHex SolanaLean.Golden.extractedPair

#guard
  let p := SolanaLean.Golden.extractedPair
  let q : SolanaLean.IR.Program :=
    { p with methods := p.methods.map fun m =>
        if m.ixName == "getLeft" then
          { m with ops := #[.returnU64 (.field (.arg 0) "right")] }
        else m }
  SolanaLean.IR.digestHex p != SolanaLean.IR.digestHex q

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains s!"digest={SolanaLean.IR.digestHex SolanaLean.Golden.extractedCounter}"
