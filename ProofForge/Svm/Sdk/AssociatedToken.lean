import ProofForge.Attr
import ProofForge.Svm.Runtime

/-!
# SVM SDK Associated Token Account facade

The source contract names the existing fixed `CreateIdempotent` composition without exposing its
instruction tag or account metas. External account 5 is the caller-supplied Token program, so the
facade does not silently substitute classic Token when the transaction is constructing a
Token-2022 associated account. The target retains account privilege and executable checks; the
selected ATA program owns derived-address validation. Program-id authentication remains future
SDK policy rather than a hidden default.

This is a compiler-erased fixed geometry, not a runtime account list or persistent allocation.
Ordinary Create, RecoverNested, alternate account ordering, and derived-address helpers remain
fail closed until their complete Runtime contracts exist.
-/

namespace ProofForge.Svm.Sdk.AssociatedToken

/-- Create the canonical associated token account if absent and accept an already initialized
account. External accounts are payer s+w / ATA w / wallet / mint / System / selected Token, with
the Associated Token Account program as callee account 6. -/
@[pf_inline] def createIdempotent : UInt64 :=
  ProofForge.Svm.Runtime.ataCreateIdempotent

end ProofForge.Svm.Sdk.AssociatedToken
