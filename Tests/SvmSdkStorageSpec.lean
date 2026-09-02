import Examples.Svm.JobQueue
import ProofForge

/-!
Focused checks for the `Svm.Sdk.Storage` persistent facade via the non-Phoenix
`Examples.Svm.JobQueue` consumer. The `#pf_build` commands run the same extraction and sBPF
emission path as the CLI without touching the shared registry; `#guard`s pin the static
descriptor geometry and the fail-closed well-formedness boundaries.
-/
namespace Tests.SvmSdkStorageSpec

open Examples.Svm.JobQueue
open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage

-- Focused extract + emit through the generic target path.
#pf_build Examples.Svm.JobQueue
#pf_build Examples.Svm.JobQueue

-- Layout descriptors are fully static and well formed.
#guard (small 1).wellFormed
#guard (small 2).wellFormed
#guard (small 1).allocator.slots ==
  { account := 1, baseWord := 5, strideWords := 1, capacity := 8
    indexBase := IndexBase.one, access := Access.programOwnedMutable }
#guard OneBasedAllocator.liveCount (small 1).allocator ==
  Field.scalar 1 2
#guard (small 1).allocator.cursor ==
  Field.scalar 1 3
#guard (small 1).jobs ==
  BoundedVec.oneBased 1 4 13 8
#guard (small 1).jobs.slots.firstWord == 13
#guard (small 1).jobs.count.firstWord == 4
#guard (small 1).jobs.capacity == 8
#guard (small 1).allocator.slots.capacity == 8

-- SDK predicates reject cross-account headers.
#guard !({ (small 1).jobs with count := Field.scalar 2 4 }).wellFormed

-- SDK predicates reject non-one-based or read-only slot regions.
#guard !({ (small 1).jobs with
  slots := { (small 1).jobs.slots with region.indexBase := IndexBase.zero } }).wellFormed
#guard !({ (small 1).jobs with
  slots := { (small 1).jobs.slots with
    region.access := { writable := false, currentProgramOwned := true } } }).wellFormed

-- SDK predicates reject header/body overlap.
#guard !({ (small 1).jobs with count := Field.scalar 1 13 }).wellFormed

-- Allocator handles compose with ordered-map geometry: same packed-cursor halves.
#guard (Allocator.ofRbMap (RbMap.key4OneBased 1 40 44 45 46 18 16)).cursor ==
  Field.scalar 1 43
#guard (RbMap.key4OneBased 1 40 44 45 46 18 16 |>.allocator).wellFormed

-- Capacity ceilings are compile-time data, enforced by the well-formedness predicate.
#guard !({ (small 1).jobs with
  slots := { (small 1).jobs.slots with region.capacity := containerCapacityLimit + 1 } }).wellFormed

end Tests.SvmSdkStorageSpec
