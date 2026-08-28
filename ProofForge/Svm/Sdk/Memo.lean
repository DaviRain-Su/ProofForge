import ProofForge.Attr
import ProofForge.Svm.Runtime

/-!
# SVM SDK Memo facade

An honest name for the existing closed Memo composition. This slice writes the fixed UTF-8 literal
`"ok"`; it does not pretend to expose dynamic strings or a bounded byte buffer. General bounded
memo data remains future Runtime/codec work.
-/

namespace ProofForge.Svm.Sdk.Memo

/-- Write the fixed UTF-8 literal `"ok"`. External account 0 signs and the Memo program is callee
account 1. -/
@[pf_inline] def writeOk : UInt64 :=
  ProofForge.Svm.Runtime.memoWrite

end ProofForge.Svm.Sdk.Memo
