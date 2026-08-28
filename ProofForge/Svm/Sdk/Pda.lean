import ProofForge.Attr
import ProofForge.Svm.Runtime

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
  !seed.isEmpty && seed.length ≤ 32 && seed.toList.all (·.toNat < 128)

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

end ProofForge.Svm.Sdk.Pda.Ascii
