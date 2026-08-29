import ProofForge.Attr
import ProofForge.Svm.Memory
import ProofForge.Svm.Runtime

/-!
# Checked SVM memory facade

Source-facing account-span wrappers for the official Solana program-memory host functions. A span
contains compile-time account/offset/length geometry only. Extraction erases it; no pointer,
slice header, heap object, or account reference can enter persistent state.
-/

namespace ProofForge.Svm.Sdk.Memory

open ProofForge.Svm.Runtime

abbrev Span := ProofForge.Svm.Memory.Span

@[pf_inline] def Span.accountData (account offsetBytes lengthBytes : Nat) : Span :=
  { account, offsetBytes, lengthBytes }

/-- Official non-overlapping copy. Malformed or overlapping static spans fail extraction. -/
@[pf_inline] def copyNonoverlapping (destination source : Span) : UInt64 :=
  memoryCopy (UInt64.ofNat destination.account) (UInt64.ofNat destination.offsetBytes)
    (UInt64.ofNat source.account) (UInt64.ofNat source.offsetBytes)
    (UInt64.ofNat destination.lengthBytes)

/-- Official overlap-safe move. -/
@[pf_inline] def move (destination source : Span) : UInt64 :=
  memoryMove (UInt64.ofNat destination.account) (UInt64.ofNat destination.offsetBytes)
    (UInt64.ofNat source.account) (UInt64.ofNat source.offsetBytes)
    (UInt64.ofNat destination.lengthBytes)

/-- Official byte fill; only the low eight bits of `byte` are written. -/
@[pf_inline] def set (destination : Span) (byte : UInt64) : UInt64 :=
  memorySet (UInt64.ofNat destination.account) (UInt64.ofNat destination.offsetBytes)
    (UInt64.ofNat destination.lengthBytes) byte

/-- Exact `sol_memcmp_` signed-i32 result represented by its zero-extended 32-bit bit pattern. -/
@[pf_inline] def compareI32Bits (left right : Span) : UInt64 :=
  memoryCompare (UInt64.ofNat left.account) (UInt64.ofNat left.offsetBytes)
    (UInt64.ofNat right.account) (UInt64.ofNat right.offsetBytes)
    (UInt64.ofNat left.lengthBytes)

end ProofForge.Svm.Sdk.Memory
