import Examples.TicketLine
import ProofForge

/-!
Focused checks for the `Svm.Sdk.Queue` fixed-capacity FIFO and the `Svm.Sdk.Storage`
POD/ordered-map handles via the non-Phoenix `Examples.TicketLine` consumer. The `#pf_build`
commands run the same extraction and sBPF emission path as the CLI without touching the
shared registry; `#guard`s pin the static descriptor geometry and the fail-closed
well-formedness boundaries.
-/
namespace Tests.SvmSdkQueueSpec

open Examples.TicketLine
open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Queue
open ProofForge.Svm.Sdk.Storage

-- Focused extract + emit through the generic target path.
#pf_build Examples.TicketLine
#pf_build Examples.TicketLine

-- Layout descriptors are fully static and well formed.
#guard (small 1).wellFormed
#guard (small 2).wellFormed
#guard (small 1).line ==
  BoundedQueue.oneBased 1 2 4 16
#guard (small 1).line.head.firstWord == 2
#guard (small 1).line.count.firstWord == 3
#guard (small 1).line.slots.firstWord == 4
#guard (small 1).line.capacity == 16
#guard (small 1).status.field ==
  Field.oneBased 1 20 1 16
#guard (small 1).registry.map ==
  RbMap.key4OneBased 1 40 44 45 46 18 16
#guard (small 1).owner.field.firstWord == 50
#guard (small 1).owner.field.region.sameShape (small 1).registry.map.links.region

-- Queue predicates reject cross-account headers and header/body overlap.
#guard !({ (small 1).line with head := Field.scalar 2 2 }).wellFormed
#guard !({ (small 1).line with count := Field.scalar 1 4 }).wellFormed
#guard !({ (small 1).line with head := Field.scalar 1 6 }).wellFormed

-- Queue predicates reject non-adjacent or unwritable headers.
#guard !({ (small 1).line with count := Field.scalar 1 9 }).wellFormed
#guard !({ (small 1).line with
  head := { (small 1).line.head with
    region.access := { writable := true, currentProgramOwned := false } } }).wellFormed

-- POD/ordered-map handles compose: the registry allocator and owner column share geometry.
#guard (small 1).registry.allocator.wellFormed
#guard (small 1).registry.allocator.liveCount.firstWord == 42
#guard (small 1).registry.allocator.cursor.firstWord == 43
#guard !({ (small 1).registry with
  map := RbMap.key4OneBased 1 41 44 45 46 18 16 }).wellFormed

end Tests.SvmSdkQueueSpec
