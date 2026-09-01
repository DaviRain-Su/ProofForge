import Examples.MemberDirectory
import Examples.UniqueRoster
import ProofForge

/-!
Focused shared policy, derived compact geometry, and extraction checks for the SVM persistent
bounded enumerable set. Runtime mutation and rollback are covered by Mollusk.
-/

namespace Tests.SvmSdkStorageEnumerableSetSpec

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.StorageEnumerableSet

#pf_build Examples.MemberDirectory
#pf_build Examples.UniqueRoster

private def directory := Examples.MemberDirectory.members 1
private def roster := Examples.UniqueRoster.roster 1

#guard directory.wellFormed
#guard roster.wellFormed
#guard directory.capacity == 4 && roster.capacity == 5
#guard directory.values == Field.oneBased 1 2 1 4
#guard directory.positions == Field.oneBased 1 16 7 4
#guard directory.index == RbMap.key4OneBased 1 6 10 11 12 7 4
#guard roster.values == Field.oneBased 1 3 1 5
#guard roster.positions == Field.oneBased 1 18 7 5
#guard roster.index == RbMap.key4OneBased 1 8 12 13 14 7 5

private def aliasedValues : Descriptor :=
  { directory with values := Field.oneBased 1 3 1 4 }

private def wrongPositions : Descriptor :=
  { directory with positions := Field.oneBased 1 15 7 4 }

#guard !aliasedValues.wellFormed
#guard !wrongPositions.wellFormed

-- Shared target-neutral position+1 and swap-remove policy.
#guard countWellFormed 4 0 && countWellFormed 4 4 && !countWellFormed 4 5
#guard positionLive 1 1 && positionLive 4 4
#guard !positionLive 0 4 && !positionLive 5 4
#guard isPresentAt 2 3 9 9 && !isPresentAt 2 3 8 9
#guard canValueAt 4 3 0 && canValueAt 4 3 2
#guard !canValueAt 4 3 3 && !canValueAt 4 5 0

-- Index-scan / removeAt / clear are compile-time facade composition (no new Runtime leaf).
#guard directory.canIndex 0 == false  -- empty live prefix
#guard (directory.clear) == (directory.initialize)

end Tests.SvmSdkStorageEnumerableSetSpec
