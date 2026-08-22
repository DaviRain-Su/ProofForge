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
import Examples.SysXfer
import Tests.Fixtures

#solana_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.get

#solana_extract Examples.Counter.init Examples.Counter.decrement Examples.Counter.get

#solana_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft

#solana_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft with "left", "right"

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesNat
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.usesNat Examples.Counter.increment Examples.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract Examples.Counter.init Tests.Fixtures.wrappingAdd Examples.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract Examples.Counter.init Tests.Fixtures.wrappingSub Examples.Counter.get

/--
error: extract/unsupported: field flag is not a supported leaf
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.initFlag Tests.Fixtures.creditFlag Tests.Fixtures.getFlagValue

/--
error: extract/unsupported: fields #[value] != inferred #[left, right]
-/
#guard_msgs (error) in
#solana_extract Examples.Pair.init Examples.Pair.creditLeft Examples.Pair.getLeft with "value"

#solana_extract Examples.Counter.init Examples.Counter.scale Examples.Counter.get

#solana_extract Examples.Counter.init Examples.Counter.divide Examples.Counter.get

#solana_extract Examples.Counter.init Examples.Counter.modulo Examples.Counter.get

#solana_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.nonzero

#solana_extract Examples.Flag.init Examples.Flag.setFlag Examples.Flag.getFlag

#solana_extract Examples.Maybe.init Examples.Maybe.setSome Examples.Maybe.isSome

#solana_extract Examples.Maybe.init Examples.Maybe.setSome Examples.Maybe.getValue

#solana_extract Examples.Window.init Examples.Window.setTail Examples.Window.getHead

#solana_extract Examples.Phase.init Examples.Phase.setLive Examples.Phase.isLive

#solana_extract Examples.Choice.init Examples.Choice.setHold Examples.Choice.getHeld

#solana_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.height

#solana_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.era

#solana_extract Examples.Clock.init Examples.Clock.stamp Examples.Clock.key0

#solana_extract Examples.Transfer.init Examples.Transfer.transfer Examples.Transfer.get

#solana_extract Examples.Ping.init Examples.Ping.ping Examples.Ping.get

#solana_extract Examples.Call.init Examples.Call.call Examples.Call.get

#solana_extract Examples.Info.init Examples.Info.touch Examples.Info.lamports

#solana_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.bump

#solana_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.check

#solana_extract Examples.Pda.init Examples.Pda.touch Examples.Pda.checkBad

#solana_extract Examples.Signed.init Examples.Signed.signed Examples.Signed.get

#solana_extract Examples.Create.init Examples.Create.create Examples.Create.get

#solana_extract Examples.TokenXfer.init Examples.TokenXfer.send Examples.TokenXfer.get

#solana_extract Examples.Ata.init Examples.Ata.openAta Examples.Ata.get

#solana_extract Examples.Rent.init Examples.Rent.stamp Examples.Rent.exempt

#solana_extract Examples.TokenMint.init Examples.TokenMint.mintTo Examples.TokenMint.get

#solana_extract Examples.SysAlloc.init Examples.SysAlloc.alloc Examples.SysAlloc.get

#solana_extract Examples.SysAlloc.init Examples.SysAlloc.assign Examples.SysAlloc.get

#solana_extract Examples.TokenAcc.init Examples.TokenAcc.openAcc Examples.TokenAcc.get

#solana_extract Examples.TokenAcc.init Examples.TokenAcc.closeAcc Examples.TokenAcc.get

#solana_extract Examples.Memo.init Examples.Memo.write Examples.Memo.get

#solana_extract Examples.CreatePda.init Examples.CreatePda.openPda Examples.CreatePda.get

#solana_extract Examples.CreatePda.init Examples.CreatePda.openBad Examples.CreatePda.get

#solana_extract Examples.TokenApprove.init Examples.TokenApprove.approve Examples.TokenApprove.get

#solana_extract Examples.TokenFreeze.init Examples.TokenFreeze.freeze Examples.TokenFreeze.get

#solana_extract Examples.TokenFreeze.init Examples.TokenFreeze.thaw Examples.TokenFreeze.get

#solana_extract Examples.TokenAuth.init Examples.TokenAuth.setAuth Examples.TokenAuth.get

#solana_extract Examples.TokenAuth.init Examples.TokenAuth.revoke Examples.TokenAuth.get

#solana_extract Examples.Epoch.init Examples.Epoch.stamp Examples.Epoch.span

#solana_extract Examples.TokenSize.init Examples.TokenSize.size Examples.TokenSize.get

#solana_extract Examples.SysSeed.init Examples.SysSeed.openSeed Examples.SysSeed.get

#solana_extract Examples.SysSeed.init Examples.SysSeed.createSeed Examples.SysSeed.get

#solana_extract Examples.SysSeed.init Examples.SysSeed.assignSeed Examples.SysSeed.get

#solana_extract Examples.SysXfer.init Examples.SysXfer.sendSeed Examples.SysXfer.get

/--
error: extract/unsupported: field tag enum has payload
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.initTagged Tests.Fixtures.setTagged Tests.Fixtures.getTagged

/--
error: extract/unsupported: field items Array is not fixed-length; use Vector
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.initBag Tests.Fixtures.setBagHead Tests.Fixtures.getBagHead

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract Examples.Counter.init Tests.Fixtures.wrappingMul Examples.Counter.get
