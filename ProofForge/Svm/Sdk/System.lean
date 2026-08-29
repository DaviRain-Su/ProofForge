import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.Seed

/-!
# SVM SDK System Program facade

Stable source names for fixed-account System Program effects. These functions erase to the
existing generic Runtime invoke contract; they do not introduce plan objects, dynamic account
tables, operations, or emitter recipes.
-/

namespace ProofForge.Svm.Sdk.System

/-- Closed `system.transfer`: account 0 is the signer/writable payer and account 1 is writable. -/
@[pf_inline] def transfer (lamports : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemTransfer lamports

/-- Closed `system.createAccount`: account 0 is payer, account 1 is the new signer account, and
the owner is the current program id. Both instruction values may be dynamic scalars. -/
@[pf_inline] def createAccount (lamports space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemCreate lamports space

/-- Closed `system.assign`: re-points account 0 (signer + writable) at the current program id.
Fixed geometry: outer account 0 is the signer/writable target, outer account 1 is the System
program. -/
@[pf_inline] def assign : UInt64 :=
  ProofForge.Svm.Runtime.systemAssign

/-- Closed `system.allocate`: reserves `space` bytes on account 0 (signer + writable).
Fixed geometry: outer account 0 is the signer/writable target, outer account 1 is the System
program; `space` may be a dynamic scalar instruction value. -/
@[pf_inline] def allocate (space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemAllocate space

/-- Closed `system advance_nonce_account` (tag 4). Fixed geometry: outer account 0 is the nonce
authority (signer), outer account 1 is the writable nonce account, outer account 2 is
recent blockhashes, and outer account 3 is the System program. -/
@[pf_inline] def advanceNonce : UInt64 :=
  ProofForge.Svm.Runtime.systemAdvanceNonce

/-!
## Seed-derived accounts

These calls accept one compile-time ASCII seed and encode its byte length next to the literal.
The extractor enforces the same 1–32-byte seven-bit policy as `Sdk.Pda.Ascii`; account geometry
remains fixed and no seed bytes or pointers enter persistent account state.
-/

namespace AsciiSeed

/-- Host-visible preflight for the target verifier's 1–32-byte seven-bit seed policy. -/
def wellFormed (seed : String) : Bool :=
  ProofForge.Svm.Seed.Ascii.wellFormed seed

/-- Allocate `space` bytes on `create_with_seed(base, seed, currentProgram)`.
External account 0 is the signer base, account 1 is the writable derived account, and account 2 is
the System program. -/
@[pf_inline] def allocate (seed : String) (space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 9, .accKey 0, .u64le (UInt64.ofNat seed.length), .ascii seed,
      .u64le space, .programId]

/-- Transfer `lamports` and allocate `space` bytes for
`create_with_seed(base, seed, currentProgram)`. External account 0 is the signer/writable payer and
base, account 1 is the writable derived account, and account 2 is the System program. -/
@[pf_inline] def createAccount (seed : String) (lamports space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    #[.u32le 3, .accKey 0, .u64le (UInt64.ofNat seed.length), .ascii seed,
      .u64le lamports, .u64le space, .programId]

/-- Assign `create_with_seed(base, seed, currentProgram)` to the current program.
External account 0 is the signer base, account 1 is the writable derived account, and account 2 is
the System program. -/
@[pf_inline] def assign (seed : String) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 10, .accKey 0, .u64le (UInt64.ofNat seed.length), .ascii seed, .programId]

/-- Transfer `lamports` from `create_with_seed(base, seed, currentProgram)` to account 2.
External account 0 is the signer base, account 1 is the writable derived payer, account 2 is the
writable recipient, and account 3 is the System program. -/
@[pf_inline] def transfer (seed : String) (lamports : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false },
      { acc := 2, signer := false, writable := true }]
    #[.u32le 11, .u64le lamports, .u64le (UInt64.ofNat seed.length), .ascii seed, .programId]


section Proofs

/-- wf → seed 非空。 -/
theorem seed_wf_nonEmpty (seed : String) (h : wellFormed seed = true) :
    seed.length ≠ 0 := by
  unfold wellFormed ProofForge.Svm.Seed.Ascii.wellFormed at h
  simp at h
  intro hlen
  have hempty : seed = "" := by simp [String.length] at hlen; exact hlen
  exact h.1.1 hempty

/-- wf → seed 长度 ≤ 32。 -/
theorem seed_wf_bounded (seed : String) (h : wellFormed seed = true) :
    seed.length ≤ 32 := by
  unfold wellFormed ProofForge.Svm.Seed.Ascii.wellFormed at h
  simp at h
  exact h.1.2

end Proofs

end AsciiSeed




end ProofForge.Svm.Sdk.System

