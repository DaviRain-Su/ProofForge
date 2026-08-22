import SolanaLean
import Tests.Fixtures

#solana_extract SolanaLean.Counter.init SolanaLean.Counter.increment SolanaLean.Counter.get

#solana_extract SolanaLean.Counter.init SolanaLean.Counter.decrement SolanaLean.Counter.get

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesNat
-/
#guard_msgs (error) in
#solana_extract Tests.Fixtures.usesNat SolanaLean.Counter.increment SolanaLean.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract SolanaLean.Counter.init Tests.Fixtures.wrappingAdd SolanaLean.Counter.get

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract SolanaLean.Counter.init Tests.Fixtures.wrappingSub SolanaLean.Counter.get
