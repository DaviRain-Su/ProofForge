import SolanaLean
import Examples.Counter
import Examples.Pair
import Examples.Flag
import Examples.Maybe
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

/--
error: extract/unsupported: mutating method missing checked arith
-/
#guard_msgs (error) in
#solana_extract Examples.Counter.init Tests.Fixtures.wrappingMul Examples.Counter.get
