import ProofForge.Attr
import ProofForge.Svm.Runtime

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

end ProofForge.Svm.Sdk.System
