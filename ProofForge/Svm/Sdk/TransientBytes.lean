import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.TransientBytes

/-!
# Source-facing invocation-local byte buffer

This is the bounded counterpart of a serialized-record byte writer over on-chain Rust's bump heap:
capacity is compile-time fixed in bytes, payload allocation is invocation-only, growth never
reallocates, and `finish` does not reclaim the Solana bump heap. Every stored byte is validated
against the canonical `≤ 255` range, `appendLe64` writes exactly eight little-endian bytes, and
OOM, full capacity, out-of-bounds access, out-of-range byte values, and stale handles are explicit
terminal program errors. The native pointer never reaches a source or account value.

Two same-kind compile-time handles can be active in one invocation, alongside the two `Vector64`
slots: `bounded` opens the historical slot 0 and `boundedAlt` opens slot 1. Both slots decode to
the same runtime leaves — the slot rides inside the compiler-erased capacity word shared by the
whole `Sdk.Transient` — and each owns a private metadata bank and disjoint payload region while
the other handle stays live.
-/

namespace ProofForge.Svm.Sdk.Transient

open ProofForge.Svm.Runtime

abbrev Bytes := ProofForge.Svm.TransientBytes.Config

/-- Slot-0 bounded byte buffer: the historical handle encoding. -/
@[pf_inline] def Bytes.bounded (capacity : Nat) : Bytes :=
  { capacity }

/-- Slot-1 bounded byte buffer: same byte capacity, private metadata bank and payload region.
The slot is additive on literals inside the erased capacity word, so extraction still sees one
static `UInt64` argument and no new runtime leaf. -/
@[pf_inline] def Bytes.boundedAlt (capacity : Nat) : Bytes :=
  { capacity := ProofForge.Svm.Sdk.Transient.secondSlotWord capacity }

@[pf_inline] def Bytes.begin (bytes : Bytes) : UInt64 :=
  transientBytesBegin (UInt64.ofNat bytes.capacity)

@[pf_inline] def Bytes.push (bytes : Bytes) (byte : UInt64) : UInt64 :=
  transientBytesPush (UInt64.ofNat bytes.capacity) byte

@[pf_inline] def Bytes.appendLe64 (bytes : Bytes) (value : UInt64) : UInt64 :=
  transientBytesAppendLe64 (UInt64.ofNat bytes.capacity) value

@[pf_inline] def Bytes.set (bytes : Bytes) (index byte : UInt64) : UInt64 :=
  transientBytesSet (UInt64.ofNat bytes.capacity) index byte

/-- Shorten the live prefix to `newLength`; a length at or above the current length is a no-op. -/
@[pf_inline] def Bytes.truncate (bytes : Bytes) (newLength : UInt64) : UInt64 :=
  transientBytesTruncate (UInt64.ofNat bytes.capacity) newLength

@[pf_inline] def Bytes.clear (bytes : Bytes) : UInt64 :=
  transientBytesClear (UInt64.ofNat bytes.capacity)

@[pf_inline] def Bytes.finish (bytes : Bytes) : UInt64 :=
  transientBytesFinish (UInt64.ofNat bytes.capacity)

@[pf_inline] def Bytes.length (bytes : Bytes) : UInt64 :=
  transientBytesLength (UInt64.ofNat bytes.capacity)

@[pf_inline] def Bytes.get (bytes : Bytes) (index : UInt64) : UInt64 :=
  transientBytesGet (UInt64.ofNat bytes.capacity) index

/-- Remove and return the final live byte. Empty buffers fail with the bounded-index error. -/
@[pf_inline] def Bytes.pop (bytes : Bytes) : UInt64 :=
  transientBytesPop (UInt64.ofNat bytes.capacity)

/-- Publish exactly one official `sol_log_data` field whose bytes are the active payload and whose
length is the current runtime length. The syscall descriptor is constructed by the target emitter;
no pointer, descriptor, or syscall enters this source handle. -/
@[pf_inline] def Bytes.logData (bytes : Bytes) : UInt64 :=
  transientBytesLogData (UInt64.ofNat bytes.capacity)

end ProofForge.Svm.Sdk.Transient
