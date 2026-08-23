import ProofForge
import Examples.Counter
import Examples.Pair
import Examples.Flag
import Examples.Maybe
import Examples.Window
import Examples.Phase
import Examples.Choice
import Examples.Clock
import Examples.Transfer
import Examples.EvmCtx
import Examples.TipJar
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
import Tests.Fixtures

open Lean Elab Command

#pf_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.get

#pf_extract Examples.Counter.init Examples.Counter.decrement Examples.Counter.get

#pf_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft

#pf_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft with "left", "right"

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesNat
-/
#guard_msgs (error) in
#pf_extract Tests.Fixtures.usesNat Examples.Counter.increment Examples.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#pf_extract Examples.Counter.init Tests.Fixtures.wrappingAdd Examples.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#pf_extract Examples.Counter.init Tests.Fixtures.wrappingSub Examples.Counter.get

/--
error: extract/unsupported: field flag enum has payload
-/
#guard_msgs (error) in
#pf_extract Tests.Fixtures.initFlag Tests.Fixtures.creditFlag Tests.Fixtures.getFlagValue

/--
error: extract/unsupported: fields #[value] != inferred #[left, right]
-/
#guard_msgs (error) in
#pf_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft with "value"

#pf_extract Examples.Counter.init Examples.Counter.scale Examples.Counter.get

#pf_extract Examples.Counter.init Examples.Counter.divide Examples.Counter.get

#pf_extract Examples.Counter.init Examples.Counter.modulo Examples.Counter.get

#pf_extract Tests.Fixtures.initFold Tests.Fixtures.runFold Tests.Fixtures.foldProduct

elab "#pf_guard_state_fold_ir" : command => do
  let env ← getEnv
  let program ←
    match ProofForge.Extract.extractProgram env ``Tests.Fixtures.initFold
        ``Tests.Fixtures.runFold ``Tests.Fixtures.foldProduct with
    | .ok p => pure p
    | .error reason => throwError reason
  let some run := program.methods.find? (·.ixName == "runFold")
    | throwError "missing state-fold method"
  let expected : Array ProofForge.Ops.Op := #[
    .forBody 2 #[
      .ite .eq .loopIx (.lit 0)
        #[.storeField "product" (.mulU64 (.arg 0) (.arg 1))]
        #[
          .storeField "quotient" (.divU64 (.arg 0) (.arg 1)),
          .storeField "remainder" (.modU64 (.arg 0) (.arg 1))
        ]
    ],
    .okState (.field (.arg 2) "product")
  ]
  unless run.ops == expected do
    throwError s!"state-fold IR mismatch: {repr run.ops}"

#pf_guard_state_fold_ir

#pf_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.nonzero

#pf_extract Examples.Flag.init Examples.Flag.setFlag Examples.Flag.getFlag

#pf_extract Examples.Maybe.init Examples.Maybe.setSome Examples.Maybe.isSome

#pf_extract Examples.Maybe.init Examples.Maybe.setSome Examples.Maybe.getValue

#pf_extract Examples.Window.init Examples.Window.setTail Examples.Window.getHead

#pf_extract Examples.Phase.init Examples.Phase.setLive Examples.Phase.isLive

#pf_extract Examples.Choice.init Examples.Choice.setHold Examples.Choice.getHeld

#pf_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.height

#pf_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.era

#pf_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.key0

#pf_extract Examples.Transfer.init Examples.Transfer.transfer Examples.Transfer.get

#pf_extract Examples.Ping.init Examples.Ping.ping Examples.Ping.get

#pf_extract Examples.Call.init Examples.Call.call Examples.Call.get

#pf_extract Examples.Info.init Examples.Info.touch Examples.Info.lamports

#pf_extract Examples.Peer.init Examples.Peer.touch Examples.Peer.lamports1

#pf_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.bump

#pf_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.check

#pf_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.checkBad

#pf_extract Examples.Signed.init Examples.Signed.signed Examples.Signed.get

#pf_extract Examples.Create.init Examples.Create.create Examples.Create.get

#pf_extract Examples.TokenXfer.init Examples.TokenXfer.send Examples.TokenXfer.get

#pf_extract Examples.Ata.init Examples.Ata.openAta Examples.Ata.get

#pf_extract Examples.Rent.init Examples.Rent.stamp Examples.Rent.exempt

#pf_extract Examples.TokenMint.init Examples.TokenMint.mintTo Examples.TokenMint.get

#pf_extract Examples.SysAlloc.init Examples.SysAlloc.alloc Examples.SysAlloc.get

#pf_extract Examples.SysAlloc.init Examples.SysAlloc.assign Examples.SysAlloc.get

#pf_extract Examples.TokenAcc.init Examples.TokenAcc.openAcc Examples.TokenAcc.get

#pf_extract Examples.TokenAcc.init Examples.TokenAcc.closeAcc Examples.TokenAcc.get

#pf_extract Examples.Memo.init Examples.Memo.write Examples.Memo.get

#pf_extract Examples.CreatePda.init Examples.CreatePda.openPda Examples.CreatePda.get

#pf_extract Examples.CreatePda.init Examples.CreatePda.openBad Examples.CreatePda.get

#pf_extract Examples.TokenApprove.init Examples.TokenApprove.approve Examples.TokenApprove.get

#pf_extract Examples.TokenFreeze.init Examples.TokenFreeze.freeze Examples.TokenFreeze.get

#pf_extract Examples.TokenFreeze.init Examples.TokenFreeze.thaw Examples.TokenFreeze.get

#pf_extract Examples.TokenAuth.init Examples.TokenAuth.setAuth Examples.TokenAuth.get

#pf_extract Examples.TokenAuth.init Examples.TokenAuth.revoke Examples.TokenAuth.get

#pf_extract Examples.Epoch.init Examples.Epoch.stamp Examples.Epoch.span

#pf_extract Examples.TokenSize.init Examples.TokenSize.size Examples.TokenSize.get

#pf_extract Examples.SysSeed.init Examples.SysSeed.openSeed Examples.SysSeed.get

#pf_extract Examples.SysSeed.init Examples.SysSeed.createSeed Examples.SysSeed.get

#pf_extract Examples.SysSeed.init Examples.SysSeed.assignSeed Examples.SysSeed.get

#pf_extract Examples.SysXfer.init Examples.SysXfer.sendSeed Examples.SysXfer.get

#pf_extract Examples.TokenMint2.init Examples.TokenMint2.openMint Examples.TokenMint2.get

#pf_extract Examples.TokenNative.init Examples.TokenNative.syncNative Examples.TokenNative.get

#pf_extract Examples.Hash.init Examples.Hash.touch Examples.Hash.vault

#pf_extract Examples.Hash.init Examples.Hash.touch Examples.Hash.ok

#pf_extract Examples.Hash.init Examples.Hash.touch Examples.Hash.empty

#pf_extract Examples.Keys.init Examples.Keys.touch Examples.Keys.key00

#pf_extract Examples.Keys.init Examples.Keys.touch Examples.Keys.key10

#pf_extract Examples.Keccak.init Examples.Keccak.touch Examples.Keccak.vault

#pf_extract Examples.Keccak.init Examples.Keccak.touch Examples.Keccak.empty

#pf_extract Examples.Trio.init Examples.Trio.touch Examples.Trio.lamports2

#pf_extract Examples.Trio.init Examples.Trio.touch Examples.Trio.needSig1

#pf_extract Examples.Trio.init Examples.Trio.touch Examples.Trio.self2

#pf_extract Examples.Gate.init Examples.Gate.openGate Examples.Gate.now

#pf_extract Examples.Nonce.init Examples.Nonce.advance Examples.Nonce.get

#pf_extract Examples.TokenOwner.init Examples.TokenOwner.setOwner Examples.TokenOwner.get

#pf_extract Examples.TokenMs.init Examples.TokenMs.openMs Examples.TokenMs.get

/--
error: extract/unsupported: svm rejects evm leaf
-/
#guard_msgs (error) in
#pf_extract Examples.TipJar.init Examples.TipJar.deposit Examples.TipJar.get

/--
error: extract/unsupported: field tag enum has payload
-/
#guard_msgs (error) in
#pf_extract Tests.Fixtures.initTagged Tests.Fixtures.setTagged Tests.Fixtures.getTagged

/--
error: extract/unsupported: field items Array is not fixed-length; use Vector
-/
#guard_msgs (error) in
#pf_extract Tests.Fixtures.initBag Tests.Fixtures.setBagHead Tests.Fixtures.getBagHead

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#pf_extract Examples.Counter.init Tests.Fixtures.wrappingMul Examples.Counter.get
