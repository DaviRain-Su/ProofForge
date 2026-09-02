import ProofForge
import Examples.Counter
import Examples.Pair
import Examples.Svm.Nested
import Examples.Svm.Tree
import Examples.Flag
import Examples.Maybe
import Examples.Window
import Examples.Svm.Book
import Examples.Svm.Seat
import Examples.Phase
import Examples.Svm.Choice
import Examples.Svm.Clock
import Examples.Svm.Transfer
import Examples.Evm.EvmCtx
import Examples.Evm.TipJar
import Examples.Lang
import Examples.Evm.Vault
import Examples.Evm.Ownable
import Examples.Evm.Token
import Examples.Evm.Capped
import Examples.Svm.Ping
import Examples.Svm.Call
import Examples.Svm.Info
import Examples.Svm.Peer
import Examples.Svm.Pda
import Examples.Svm.Signed
import Examples.Svm.Create
import Examples.Svm.TokenXfer
import Examples.Svm.Token2022
import Examples.Svm.Ata
import Examples.Svm.Rent
import Examples.Svm.TokenMint
import Examples.Svm.SysAlloc
import Examples.Svm.TokenAcc
import Examples.Svm.Memo
import Examples.Svm.CreatePda
import Examples.Svm.TokenApprove
import Examples.Svm.TokenFreeze
import Examples.Svm.TokenAuth
import Examples.Svm.Epoch
import Examples.Svm.TokenSize
import Examples.Svm.SysSeed
import Examples.Svm.SysXfer
import Examples.Svm.TokenMint2
import Examples.Svm.TokenNative
import Examples.Svm.Hash
import Examples.Svm.Keys
import Examples.Svm.Keccak
import Examples.Svm.Trio
import Examples.Svm.Gate
import Examples.Svm.Nonce
import Examples.Svm.TokenOwner
import Examples.Svm.TokenMs
import Examples.Svm.TokenStateView
import Examples.Svm.SelfLog
import Examples.Svm.RawEntry

#pf_build Examples.Counter

#pf_build Examples.Pair

#pf_build Examples.Svm.Nested

#pf_build Examples.Svm.Tree

#pf_build Examples.Flag

#pf_build Examples.Maybe

#pf_build Examples.Window

#pf_build Examples.Svm.Book

#pf_build Examples.Svm.Seat

#pf_build Examples.Phase

#pf_build Examples.Svm.Choice

#pf_build Examples.Svm.Clock

#pf_build Examples.Svm.Transfer

#pf_build Examples.Svm.Ping

#pf_build Examples.Svm.Call

#pf_build Examples.Svm.Info

#pf_build Examples.Svm.Peer

#pf_build Examples.Svm.Pda

#pf_build Examples.Svm.Signed

#pf_build Examples.Svm.Create

#pf_build Examples.Svm.TokenXfer

#pf_build Examples.Svm.Token2022

#pf_build Examples.Svm.Ata

#pf_build Examples.Svm.Rent

#pf_build Examples.Svm.TokenMint

#pf_build Examples.Svm.SysAlloc

#pf_build Examples.Svm.TokenAcc

#pf_build Examples.Svm.Memo

#pf_build Examples.Svm.CreatePda

#pf_build Examples.Svm.TokenApprove

#pf_build Examples.Svm.TokenFreeze

#pf_build Examples.Svm.TokenAuth

#pf_build Examples.Svm.Epoch

#pf_build Examples.Svm.TokenSize

#pf_build Examples.Svm.SysSeed

#pf_build Examples.Svm.SysXfer

#pf_build Examples.Svm.TokenMint2

#pf_build Examples.Svm.TokenNative

#pf_build Examples.Svm.Hash

#pf_build Examples.Svm.Keys

#pf_build Examples.Svm.Keccak

#pf_build Examples.Svm.Trio

#pf_build Examples.Svm.Gate

#pf_build Examples.Svm.Nonce

#pf_build Examples.Svm.TokenOwner

#pf_build Examples.Svm.TokenMs

#pf_build Examples.Svm.TokenStateView

#pf_build Examples.Svm.SelfLog

#pf_build Examples.Svm.RawEntry

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.EvmCtx

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.TipJar

#pf_build Examples.Lang

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.Vault

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.Ownable

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.Token

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_build Examples.Evm.Capped

/--
error: extract/unsupported: no pf_entry
-/
#guard_msgs (error) in
#pf_build Tests.Fixtures

#guard
  match ProofForge.Svm.ABI.discHexOf "decrement" 1 with
  | .ok "0x1b92f24dfb29d300" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "creditLeft" 1 with
  | .ok "0xca5ea3052ea3b57e" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "getLeft" 0 with
  | .ok "0xe391a39d1496f393" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "scale" 1 with
  | .ok "0x5f760731ac44bf15" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "nonzero" 0 with
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
  ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedCounter ==
    ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedCounter

#guard
  ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedCounter !=
    ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedPair

#guard
  let p := ProofForge.Golden.extractedPair
  let q : ProofForge.Extract.Legacy.Program :=
    { p with methods := p.methods.map fun m =>
        if m.ixName == "getLeft" then
          { m with ops := #[.returnU64 (.field (.arg 0) "right")] }
        else m }
  ProofForge.Extract.Legacy.digestHex p != ProofForge.Extract.Legacy.digestHex q

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok asm =>
      asm.contains s!"digest={ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedCounter}"
