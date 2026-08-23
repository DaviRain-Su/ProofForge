import ProofForge
import Examples.Counter
import Examples.Pair
import Examples.Nested
import Examples.Flag
import Examples.Maybe
import Examples.Window
import Examples.Book
import Examples.Seat
import Examples.Phase
import Examples.Choice
import Examples.Clock
import Examples.Transfer
import Examples.EvmCtx
import Examples.TipJar
import Examples.Lang
import Examples.Vault
import Examples.Ownable
import Examples.Token
import Examples.Ping
import Examples.Call
import Examples.Info
import Examples.Peer
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
import Examples.SysXfer
import Examples.TokenMint2
import Examples.TokenNative
import Examples.Hash
import Examples.Keys
import Examples.Keccak
import Examples.Trio
import Examples.Gate
import Examples.Nonce
import Examples.TokenOwner
import Examples.TokenMs
import Projects.Phoenix


#pf_build Examples.Counter

#pf_build Examples.Pair

#pf_build Examples.Nested

#pf_build Examples.Flag

#pf_build Examples.Maybe

#pf_build Examples.Window

#pf_build Examples.Book

#pf_build Examples.Seat

#pf_build Examples.Phase

#pf_build Examples.Choice

#pf_build Examples.Clock

#pf_build Examples.Transfer

#pf_build Examples.Ping

#pf_build Examples.Call

#pf_build Examples.Info

#pf_build Examples.Peer

#pf_build Examples.Pda

#pf_build Examples.Signed

#pf_build Examples.Create

#pf_build Examples.TokenXfer

#pf_build Examples.Ata

#pf_build Examples.Rent

#pf_build Examples.TokenMint

#pf_build Examples.SysAlloc

#pf_build Examples.TokenAcc

#pf_build Examples.Memo

#pf_build Examples.CreatePda

#pf_build Examples.TokenApprove

#pf_build Examples.TokenFreeze

#pf_build Examples.TokenAuth

#pf_build Examples.Epoch

#pf_build Examples.TokenSize

#pf_build Examples.SysSeed

#pf_build Examples.SysXfer

#pf_build Examples.TokenMint2

#pf_build Examples.TokenNative

#pf_build Examples.Hash

#pf_build Examples.Keys

#pf_build Examples.Keccak

#pf_build Examples.Trio

#pf_build Examples.Gate

#pf_build Examples.Nonce

#pf_build Examples.TokenOwner

#pf_build Examples.TokenMs

#pf_build Projects.Phoenix

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.EvmCtx

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.TipJar

#pf_build Examples.Lang

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Vault

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Ownable

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Token

/--
error: extract/unsupported: no pf_entry
-/
#guard_msgs (error) in
#pf_build Tests.Fixtures

#guard
  match ProofForge.IR.discHexOf "decrement" 1 with
  | .ok "0x1b92f24dfb29d300" => true
  | _ => false

#guard
  match ProofForge.IR.discHexOf "creditLeft" 1 with
  | .ok "0xca5ea3052ea3b57e" => true
  | _ => false

#guard
  match ProofForge.IR.discHexOf "getLeft" 0 with
  | .ok "0xe391a39d1496f393" => true
  | _ => false

#guard
  match ProofForge.IR.discHexOf "scale" 1 with
  | .ok "0x5f760731ac44bf15" => true
  | _ => false

#guard
  match ProofForge.IR.discHexOf "nonzero" 0 with
  | .ok "0x9d4170637dda8281" => true
  | _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains "0x1b92f24dfb29d300" &&
        asm.contains "call decrement" &&
        asm.contains "call increment"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPair with
  | .error _ => false
  | .ok asm =>
      asm.contains "0xca5ea3052ea3b57e" &&
        asm.contains "call creditLeft" &&
        asm.contains "call getLeft" &&
        !asm.contains "call increment"

#guard
  ProofForge.IR.digestHex ProofForge.Golden.extractedCounter ==
    ProofForge.IR.digestHex ProofForge.Golden.extractedCounter

#guard
  ProofForge.IR.digestHex ProofForge.Golden.extractedCounter !=
    ProofForge.IR.digestHex ProofForge.Golden.extractedPair

#guard
  let p := ProofForge.Golden.extractedPair
  let q : ProofForge.IR.Program :=
    { p with methods := p.methods.map fun m =>
        if m.ixName == "getLeft" then
          { m with ops := #[.returnU64 (.field (.arg 0) "right")] }
        else m }
  ProofForge.IR.digestHex p != ProofForge.IR.digestHex q

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains s!"digest={ProofForge.IR.digestHex ProofForge.Golden.extractedCounter}"
