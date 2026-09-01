import ProofForge.Attr
import ProofForge.Wasm.Near.Memory
import ProofForge.Wasm.Near.Runtime

/-!
# NEAR invocation-local transient memory

The first source-facing consumer of the NEAR guest-Wasm arena. `Buffer64` has compile-time bounded
geometry, one active handle per invocation, and no source-visible native pointer. `begin` zeroes
the complete payload; bounds, stale handles, capacity mismatches, and allocator OOM trap.

This is not persistent storage. Later storage collections may use the arena for invocation-local
codec/key/cache bytes, but their durable values must remain in NEAR key-value storage.
-/

namespace ProofForge.Wasm.Near.Sdk.Transient

abbrev Buffer64 := Nat

def Buffer64.wellFormed (buffer : Buffer64) : Bool :=
  Memory.buffer64CapacityValid buffer

@[pf_inline] def Buffer64.bounded (capacity : Nat) : Buffer64 :=
  capacity

@[pf_inline] def Buffer64.begin (buffer : Buffer64) : UInt64 :=
  Runtime.transientBuffer64Begin buffer

@[pf_inline] def Buffer64.set (buffer : Buffer64) (index value : UInt64) : UInt64 :=
  Runtime.transientBuffer64Set buffer index value

@[pf_inline] def Buffer64.get (buffer : Buffer64) (index : UInt64) : UInt64 :=
  Runtime.transientBuffer64Get buffer index

@[pf_inline] def Buffer64.finish (buffer : Buffer64) : UInt64 :=
  Runtime.transientBuffer64Finish buffer

end ProofForge.Wasm.Near.Sdk.Transient
