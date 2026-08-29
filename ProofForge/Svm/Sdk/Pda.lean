import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.Sdk.Sysvar
import ProofForge.Svm.Seed

/-!
# SVM SDK PDA facade

Stable source names over the existing target-owned PDA discovery, validation, and signed-create
effects. ASCII seeds and account geometry remain compile-time inputs; lamports and space remain
ordinary scalar instruction values. Extraction lowers these `pf_inline` functions to the existing
Runtime leaves and generic CPI contract, without a PDA-specific operation or emitter case.

The current extractor accepts scalar/static arguments but not String fields projected through a
source descriptor structure. The extraction-facing API therefore takes the static seed directly
instead of exposing a plan object whose execution would not work. Arbitrary runtime byte buffers,
alternate program ids, and persistent pointers remain unavailable.
-/

namespace ProofForge.Svm.Sdk.Pda.Ascii

/-- Same bounded ASCII policy as target-owned `PdaSeed.ascii`: 1–32 seven-bit bytes. -/
def wellFormed (seed : String) : Bool :=
  ProofForge.Svm.Seed.Ascii.wellFormed seed

/-- Canonical bump for one compile-time seed. The IR verifier enforces `wellFormed`. -/
@[pf_inline] def bump (seed : String) : UInt64 :=
  ProofForge.Svm.Runtime.findPda seed

/-- Validate the canonical bump for one compile-time seed. -/
@[pf_inline] def check (seed : String) : UInt64 :=
  ProofForge.Svm.Runtime.checkPda seed (ProofForge.Svm.Runtime.findPda seed)

/-- Validate an explicit bump for one compile-time seed. -/
@[pf_inline] def checkBump (seed : String) (bump : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.checkPda seed bump

/-- Create one current-program-owned PDA account. The payer/new-account/System geometry and `seed`
are static; `lamports` and `space` may be dynamic scalar instruction values. -/
@[pf_inline] def createAccount (seed : String) (lamports space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.invokeSigned 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    #[.u32le 0, .u64le lamports, .u64le space, .programId]
    seed (ProofForge.Svm.Runtime.findPda seed)

/-- Create one current-program-owned PDA with the exact current Rent minimum for one
compile-time data length. The PDA seed and account space both remain compiler-static. -/
@[pf_inline] def createRentExempt (seed : String) (space : Nat) : UInt64 :=
  createAccount seed (Sysvar.Rent.minimumBalance space) (UInt64.ofNat space)


section Proofs

/-- wf → seed 非空（String ≠ "" → length ≠ 0）。 -/
theorem wf_nonEmpty (seed : String) (h : wellFormed seed = true) :
    seed.length ≠ 0 := by
  unfold wellFormed ProofForge.Svm.Seed.Ascii.wellFormed at h
  simp at h
  intro hlen
  have hempty : seed = "" := by
    simp [String.length] at hlen
    exact hlen
  exact h.1.1 hempty

/-- wf → seed 长度 ≤ 32。 -/
theorem wf_bounded (seed : String) (h : wellFormed seed = true) :
    seed.length ≤ 32 := by
  unfold wellFormed ProofForge.Svm.Seed.Ascii.wellFormed at h
  simp at h
  exact h.1.2

end Proofs

end ProofForge.Svm.Sdk.Pda.Ascii
