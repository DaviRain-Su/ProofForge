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
-/

namespace ProofForge.Svm.Sdk.Transient

open ProofForge.Svm.Runtime

abbrev Bytes := ProofForge.Svm.TransientBytes.Config

@[pf_inline] def Bytes.bounded (capacity : Nat) : Bytes :=
  { capacity }

@[pf_inline] def Bytes.begin (bytes : Bytes) : UInt64 :=
  transientBytesBegin (UInt64.ofNat bytes.capacity)

@[pf_inline] def Bytes.push (bytes : Bytes) (byte : UInt64) : UInt64 :=
  transientBytesPush (UInt64.ofNat bytes.capacity) byte

@[pf_inline] def Bytes.appendLe64 (bytes : Bytes) (value : UInt64) : UInt64 :=
  transientBytesAppendLe64 (UInt64.ofNat bytes.capacity) value

@[pf_inline] def Bytes.set (bytes : Bytes) (index byte : UInt64) : UInt64 :=
  transientBytesSet (UInt64.ofNat bytes.capacity) index byte

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
