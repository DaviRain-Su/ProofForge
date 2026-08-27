import ProofForge
import Examples.Counter
import Tests.Fixtures

#pf_check Examples.Counter.init
#pf_check Examples.Counter.increment
#pf_check Examples.Counter.get

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesNat
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesNat

#pf_check Tests.Fixtures.usesFixedBytes12

/--
error: profile/rejected: Nat in root type Tests.Fixtures.usesDynamicFixedBytes
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesDynamicFixedBytes

/--
error: profile/rejected: partial Tests.Fixtures.loops
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.loops

/--
error: profile/rejected: axiom sorryAx
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesSorry

/--
error: profile/rejected: IO in Tests.Fixtures.usesIO
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesIO

/--
error: profile/rejected: extern Tests.Fixtures.usesExtern
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesExtern

/--
error: profile/rejected: implemented_by Tests.Fixtures.usesImplBy
-/
#guard_msgs (error) in
#pf_check Tests.Fixtures.usesImplBy
