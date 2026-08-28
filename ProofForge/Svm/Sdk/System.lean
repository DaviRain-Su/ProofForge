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

end ProofForge.Svm.Sdk.System
