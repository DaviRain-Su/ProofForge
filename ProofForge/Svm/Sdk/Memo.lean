import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.Memo

/-!
# SVM SDK Memo facade

Compiler-erased names for one statically bounded Memo composition. Payloads are compile-time
seven-bit strings of at most 512 bytes; they are copied into the existing invocation-local CPI
scratch plan and never become persistent pointers or dynamic account state.
-/

namespace ProofForge.Svm.Sdk.Memo

namespace Ascii

def maxBytes : Nat := ProofForge.Svm.Memo.Ascii.maxBytes

def wellFormed (value : String) : Bool :=
  ProofForge.Svm.Memo.Ascii.wellFormed value

/-- Write one compile-time seven-bit Memo payload. External account 0 signs and the Memo program
is callee account 1. -/
@[pf_inline] def write (value : String) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.ascii value]


/-- wf → payload 长度 ≤ Memo.Ascii.maxBytes（512）。 -/
theorem wf_bounded (value : String) (h : wellFormed value = true) :
    value.length ≤ maxBytes := by
  unfold wellFormed ProofForge.Svm.Memo.Ascii.wellFormed at h
  simp at h
  unfold maxBytes
  exact h.1

end Ascii

/-- Compatibility spelling for the original fixed payload. New applications should select their
own static payload through `Ascii.write`. -/
@[pf_inline] def writeOk : UInt64 :=
  Ascii.write "ok"

end ProofForge.Svm.Sdk.Memo
