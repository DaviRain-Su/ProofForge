import ProofForge
import ProofForge.Evm.Commands
import Examples.Counter
import Examples.Pair
import Examples.Window
import Examples.Phase
import Examples.Flag
import Examples.Maybe
import Examples.Svm.Clock
import Examples.Xrpl.XrplCtx
import Examples.Svm.Transfer
import Examples.Evm.EvmCtx
import Examples.Evm.EvmStaticCounter
import Examples.Evm.EvmStaticRoster
import Examples.Evm.EvmOrderedStorage
import Examples.Evm.EvmVecLog
import Examples.Evm.EvmVecStack
import Examples.Evm.EvmCheckpointBook
import Examples.Evm.EvmCheckpointTrace
import Examples.Evm.GuardedPayout
import Examples.Evm.TipJar
import Examples.Lang
import Examples.Evm.Vault
import Examples.Evm.Ownable
import Examples.Evm.Token
import Examples.Evm.Capped
import Examples.Evm.Wide
import Examples.Evm.Const
import Tests.Fixtures

#pf_evm_build Examples.Counter

#pf_evm_build Examples.Pair

#pf_evm_build Examples.Window

#pf_evm_build Examples.Phase

#pf_evm_build Examples.Flag

#pf_evm_build Examples.Maybe

#pf_evm_build Examples.Evm.EvmCtx

#pf_evm_build Examples.Evm.EvmStaticCounter

#pf_evm_build Examples.Evm.EvmStaticRoster

#pf_evm_build Examples.Evm.EvmOrderedStorage

#pf_evm_build Examples.Evm.EvmVecLog

#pf_evm_build Examples.Evm.EvmVecStack

#pf_evm_build Examples.Evm.EvmCheckpointBook

#pf_evm_build Examples.Evm.EvmCheckpointTrace

#pf_evm_build Examples.Evm.GuardedPayout

#pf_evm_build Examples.Evm.TipJar

#pf_evm_build Examples.Lang

#pf_evm_build Examples.Evm.Vault

#pf_evm_build Examples.Evm.Ownable

#pf_evm_build Examples.Evm.Token

#pf_evm_build Examples.Evm.Capped

#pf_evm_build Examples.Evm.Wide

#pf_evm_build Examples.Evm.Const

/--
error: extract/unsupported: evm rejects svm leaf in stamp
-/
#guard_msgs (error) in
#pf_evm_build Examples.Svm.Clock

/--
error: extract/unsupported: evm rejects xrpl leaf in stamp
-/
#guard_msgs (error) in
#pf_evm_build Examples.Xrpl.XrplCtx

/--
error: extract/unsupported: evm rejects svm leaf in transfer
-/
#guard_msgs (error) in
#pf_evm_build Examples.Svm.Transfer

/--
error: extract/unsupported: no pf_entry
-/
#guard_msgs (error) in
#pf_evm_build Tests.Fixtures
