import ProofForge
import Examples.TwoStepCounter
import Examples.Credits

/-!
R5-004 focused suite: canonical pause flags, fail-closed predicates, compatibility aliases, and
two independent consumers. Existing Anvil suites own authorization, pause/unpause, blocked-call,
and storage-atomicity behavior; canonical registry digests ensure the SDK facade adds no target
operation or artifact-visible recipe.
-/

namespace Tests.EvmPausableSpec

open ProofForge.Evm.Sdk

#guard Pausable.running == 0
#guard Pausable.paused == 1
#guard Pausable.isRunning Pausable.running
#guard !Pausable.isRunning Pausable.paused
#guard !Pausable.isRunning 2
#guard Pausable.isPaused Pausable.paused
#guard !Pausable.isPaused Pausable.running
#guard !Pausable.isPaused 2
#guard Pausable.pause Pausable.running == Pausable.paused
#guard Pausable.pause Pausable.paused == Pausable.paused
#guard Pausable.unpause Pausable.paused == Pausable.running
#guard Pausable.unpause Pausable.running == Pausable.running
#guard Pausable.violation == 0

-- Access keeps compatibility names while delegating pause semantics to the single owner.
#guard Access.runningFlag == Pausable.running
#guard Access.pausedFlag == Pausable.paused
#guard Access.requireRunning Pausable.running
#guard !Access.requireRunning Pausable.paused
#guard Access.runningViolation == Pausable.violation

open Examples.TwoStepCounter in
#guard (init ⟨1, 2, 3⟩).paused == Pausable.running

open Examples.Credits in
#guard (init ⟨1, 2, 3⟩).paused == Pausable.running

#guard ProofForge.Evm.Registry.digestOf "TwoStepCounter" == some "3b08dde14972e728"
#guard ProofForge.Evm.Registry.digestOf "Credits" == some "b419d86e92ae9e9e"

end Tests.EvmPausableSpec
