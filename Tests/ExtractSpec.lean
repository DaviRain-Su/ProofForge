import SolanaLean
import Examples.Counter
import Tests.Fixtures

#solana_extract Examples.Counter.init Examples.Counter.increment Examples.Counter.get

#solana_extract Examples.Counter.init Examples.Counter.decrement Examples.Counter.get

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
