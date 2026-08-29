import ProofForge
import ProofForge.Evm.Commands
import Examples.Counter
import Examples.Pair
import Examples.Window
import Examples.Phase
import Examples.Flag
import Examples.Maybe
import Examples.Clock
import Examples.XrplCtx
import Examples.Transfer
import Examples.EvmCtx
import Examples.EvmStaticCounter
import Examples.EvmStaticRoster
import Examples.EvmOrderedStorage
import Examples.GuardedPayout
import Examples.TipJar
import Examples.Lang
import Examples.Vault
import Examples.Ownable
import Examples.Token
import Examples.Capped
import Examples.Wide
import Examples.Const
import Tests.Fixtures

#pf_evm_build Examples.Counter

#pf_evm_build Examples.Pair

#pf_evm_build Examples.Window

#pf_evm_build Examples.Phase

#pf_evm_build Examples.Flag

#pf_evm_build Examples.Maybe

#pf_evm_build Examples.EvmCtx

#pf_evm_build Examples.EvmStaticCounter

#pf_evm_build Examples.EvmStaticRoster

#pf_evm_build Examples.EvmOrderedStorage

#pf_evm_build Examples.GuardedPayout

#pf_evm_build Examples.TipJar

#pf_evm_build Examples.Lang

#pf_evm_build Examples.Vault

#pf_evm_build Examples.Ownable

#pf_evm_build Examples.Token

#pf_evm_build Examples.Capped

#pf_evm_build Examples.Wide

#pf_evm_build Examples.Const

/--
error: extract/unsupported: evm rejects svm leaf in stamp
-/
#guard_msgs (error) in
#pf_evm_build Examples.Clock

/--
error: extract/unsupported: evm rejects xrpl leaf in stamp
-/
#guard_msgs (error) in
#pf_evm_build Examples.XrplCtx

/--
error: extract/unsupported: evm rejects svm leaf in transfer
-/
#guard_msgs (error) in
#pf_evm_build Examples.Transfer

/--
error: extract/unsupported: no pf_entry
-/
#guard_msgs (error) in
#pf_evm_build Tests.Fixtures
