import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.TransientVec

/-!
# Source-facing invocation-local UInt64 vector

This is the bounded counterpart of an on-chain Rust `Vec<u64>`: capacity is compile-time fixed,
payload allocation is invocation-only, growth never reallocates, and `finish` does not reclaim the
Solana bump heap. OOM, full capacity, out-of-bounds access, and stale handles are explicit terminal
program errors. No source or account value can contain the native pointer.
-/

namespace ProofForge.Svm.Sdk.Transient

open ProofForge.Svm.Runtime

abbrev Vector64 := ProofForge.Svm.TransientVec.Config

@[pf_inline] def Vector64.bounded (capacity : Nat) : Vector64 :=
  { capacity }

@[pf_inline] def Vector64.begin (vector : Vector64) : UInt64 :=
  transientVecBegin (UInt64.ofNat vector.capacity)

@[pf_inline] def Vector64.push (vector : Vector64) (value : UInt64) : UInt64 :=
  transientVecPush (UInt64.ofNat vector.capacity) value

@[pf_inline] def Vector64.set (vector : Vector64) (index value : UInt64) : UInt64 :=
  transientVecSet (UInt64.ofNat vector.capacity) index value

/-- Shorten the live prefix to `newLength`; a length at or above the current length is a no-op. -/
@[pf_inline] def Vector64.truncate (vector : Vector64) (newLength : UInt64) : UInt64 :=
  transientVecTruncate (UInt64.ofNat vector.capacity) newLength

@[pf_inline] def Vector64.clear (vector : Vector64) : UInt64 :=
  transientVecClear (UInt64.ofNat vector.capacity)

@[pf_inline] def Vector64.finish (vector : Vector64) : UInt64 :=
  transientVecFinish (UInt64.ofNat vector.capacity)

@[pf_inline] def Vector64.length (vector : Vector64) : UInt64 :=
  transientVecLength (UInt64.ofNat vector.capacity)

@[pf_inline] def Vector64.get (vector : Vector64) (index : UInt64) : UInt64 :=
  transientVecGet (UInt64.ofNat vector.capacity) index

/-- Remove and return the last live element. Empty vectors fail with the bounded-index error. -/
@[pf_inline] def Vector64.pop (vector : Vector64) : UInt64 :=
  transientVecPop (UInt64.ofNat vector.capacity)

end ProofForge.Svm.Sdk.Transient
