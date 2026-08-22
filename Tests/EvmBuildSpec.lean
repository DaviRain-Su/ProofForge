import SolanaLean
import SolanaLean.Evm.Commands
import Examples.Counter
import Examples.Pair
import Examples.Window
import Examples.Phase
import Examples.Clock
import Examples.Transfer
import Tests.Fixtures

#evm_build Examples.Counter

#evm_build Examples.Pair

#evm_build Examples.Window

#evm_build Examples.Phase

/--
error: extract/unsupported: evm rejects svm leaf in stamp
-/
#guard_msgs (error) in
#evm_build Examples.Clock

/--
error: extract/unsupported: evm rejects svm leaf in transfer
-/
#guard_msgs (error) in
#evm_build Examples.Transfer

/--
error: extract/unsupported: no solana_entry
-/
#guard_msgs (error) in
#evm_build Tests.Fixtures
