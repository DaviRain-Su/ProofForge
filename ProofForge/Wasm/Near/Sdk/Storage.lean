import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Runtime

/-!
# NEAR raw binary storage

`ResultBuffer` is a compile-time result bound, not a pointer or persistent collection. Every raw
storage operation replaces the single active result for the invocation; callers must consume its
status/length/bytes before issuing another storage operation.

Keys are byte-exact and unprefixed, matching nearcore and near-sdk-rs `env::storage_*`. Therefore
the caller owns namespace separation: exact compiler state-field names are reserved, and each
future collection instance must receive a unique explicit binary prefix. The SDK never invents or
silently hashes one.

Status is the exact nearcore 0/1 result:
* read/remove: absent/present;
* write: inserted/replaced;
* hasKey: absent/present.

For read/write/remove status 1, `length` is the read, evicted, or removed value length. `fits = 0`
means that length exceeded this buffer and no `read_register` copy occurred. Status 0 and hasKey
have `length = 0`, `fits = 1`. Empty keys and values use any valid positive capacity with length 0.
-/

namespace ProofForge.Wasm.Near.Sdk.Storage

open ProofForge.Core.Value

abbrev ResultBuffer := Nat

def ResultBuffer.wellFormed (buffer : ResultBuffer) : Bool :=
  Codec.storageCapacityValid buffer

@[pf_inline] def ResultBuffer.bounded (capacity : Nat) : ResultBuffer :=
  capacity

@[pf_inline] def ResultBuffer.read {keyCapacity : Nat}
    (buffer : ResultBuffer) (key : BoundedBytes keyCapacity) : UInt64 :=
  Runtime.storageRead buffer keyCapacity key

@[pf_inline] def ResultBuffer.write {keyCapacity valueCapacity : Nat}
    (buffer : ResultBuffer) (key : BoundedBytes keyCapacity)
    (value : BoundedBytes valueCapacity) : UInt64 :=
  Runtime.storageWrite buffer keyCapacity valueCapacity key value

@[pf_inline] def ResultBuffer.remove {keyCapacity : Nat}
    (buffer : ResultBuffer) (key : BoundedBytes keyCapacity) : UInt64 :=
  Runtime.storageRemove buffer keyCapacity key

@[pf_inline] def ResultBuffer.hasKey {keyCapacity : Nat}
    (buffer : ResultBuffer) (key : BoundedBytes keyCapacity) : UInt64 :=
  Runtime.storageHasKey buffer keyCapacity key

@[pf_inline] def ResultBuffer.status (buffer : ResultBuffer) : UInt64 :=
  Runtime.storageResultStatus buffer

@[pf_inline] def ResultBuffer.length (buffer : ResultBuffer) : UInt64 :=
  Runtime.storageResultLength buffer

@[pf_inline] def ResultBuffer.fits (buffer : ResultBuffer) : Bool :=
  Runtime.storageResultFits buffer != 0

@[pf_inline] def ResultBuffer.byte (buffer : ResultBuffer) (index : UInt64) : UInt8 :=
  (Runtime.storageResultByte buffer index).toUInt8

end ProofForge.Wasm.Near.Sdk.Storage
