import Examples.Svm.FeatureBits
import Examples.Svm.ClaimBits
import ProofForge

/-!
Focused geometry, packed-word policy, and extraction checks for the SVM persistent bit-set SDK.
Runtime account mutation, partial-final-word bounds, replay, and fail-closed short-account behavior
are covered by `runtime-tests/solana/tests/storage_bit_set.rs`.
-/

namespace Tests.SvmSdkStorageBitSetSpec

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageBitSet

#pf_build Examples.Svm.FeatureBits
#pf_build Examples.Svm.ClaimBits

-- Shared Core/EVM/SVM packed-word geometry.
#guard wordCount 1 == 1 && wordCount 64 == 1
#guard wordCount 65 == 2 && wordCount 128 == 2
#guard wordCount 129 == 3 && wordCount 130 == 3
#guard wordCount 130 == ProofForge.Core.Collections.bitSetWordCount 130

-- Exact account geometry and descriptor failures.
#guard (Examples.Svm.FeatureBits.flags 1).wellFormed
#guard (Examples.Svm.ClaimBits.claims 1).wellFormed
#guard (Examples.Svm.FeatureBits.flags 1).words == Field.oneBased 1 2 1 2
#guard (Examples.Svm.ClaimBits.claims 1).words == Field.oneBased 1 2 1 3
#guard !(BitSet.oneBased 0 2 128).wellFormed

private def wrongWordCount : BitSet :=
  { words := Field.oneBased 1 2 1 3, bitCapacity := 128 }

private def readonlyWords : BitSet :=
  { words := { (Examples.Svm.FeatureBits.flags 1).words with
      region.access := { writable := false, currentProgramOwned := true } }
    bitCapacity := 128 }

#guard !wrongWordCount.wellFormed
#guard !readonlyWords.wellFormed

-- Boundaries and no lower-word alias from a partial final word.
#guard inRange 130 0 && inRange 130 129
#guard !inRange 130 130 && !inRange 130 18446744073709551615
#guard wordIndexOf 0 == 0 && wordIndexOf 63 == 0
#guard wordIndexOf 64 == 1 && wordIndexOf 129 == 2
#guard wordSlotOf 0 == 1 && wordSlotOf 64 == 2 && wordSlotOf 129 == 3

-- Pure word truth table agrees with the shared packed-bit law.
#guard maskOf 0 == 1 && maskOf 63 == 9223372036854775808
#guard maskOf 64 == 1 && maskOf 129 == 2
#guard !containsOf 0 0 && containsOf 1 0 && !containsOf 1 1
#guard insertOf 0 63 == 9223372036854775808
#guard insertOf (insertOf 0 0) 63 == 9223372036854775809
#guard insertOf (insertOf 5 3) 3 == insertOf 5 3
#guard removeOf 15 0 == 14 && removeOf 15 4 == 15
#guard toggleOf 0 64 == 1 && toggleOf 1 64 == 0
#guard toggleOf (toggleOf 42 70) 70 == 42

end Tests.SvmSdkStorageBitSetSpec
