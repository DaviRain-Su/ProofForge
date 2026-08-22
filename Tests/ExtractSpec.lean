import SolanaLean
import Tests.Fixtures

#solana_extract SolanaLean.Counter.init SolanaLean.Counter.increment SolanaLean.Counter.get

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesNat
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.usesNat SolanaLean.Counter.increment SolanaLean.Counter.get

/--
error: extract/unsupported: increment not ite
-/
#guard_msgs (error) in
#solana_extract SolanaLean.Counter.init Tests.Fixtures.wrappingAdd SolanaLean.Counter.get
