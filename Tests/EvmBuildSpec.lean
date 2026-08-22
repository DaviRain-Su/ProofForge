import ProofForge
import ProofForge.Evm.Commands
import Examples.Counter
import Examples.Pair
import Examples.Window
import Examples.Phase
import Examples.Flag
import Examples.Maybe
import Examples.Clock
import Examples.Transfer
import Examples.EvmCtx
import Examples.TipJar
import Examples.Lang
import Examples.Vault
import Examples.Ownable
import Tests.Fixtures

#pf_evm_build Examples.Counter

#pf_evm_build Examples.Pair

#pf_evm_build Examples.Window

#pf_evm_build Examples.Phase

#pf_evm_build Examples.Flag

#pf_evm_build Examples.Maybe

#pf_evm_build Examples.EvmCtx

#pf_evm_build Examples.TipJar

#pf_evm_build Examples.Lang

#pf_evm_build Examples.Vault

#pf_evm_build Examples.Ownable

/--
error: extract/unsupported: evm rejects svm leaf in stamp
-/
#guard_msgs (error) in
#pf_evm_build Examples.Clock

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
