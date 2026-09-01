import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.Memo

/-!
# SVM SDK Memo facade

Compiler-erased names for statically bounded Memo compositions. ASCII payloads are compile-time
seven-bit strings of at most 512 bytes. UTF-8 payloads are compile-time strings whose UTF-8 byte
encoding is at most 512 bytes and passes a strict Unicode-scalar scan. Both erase into the existing
invocation-local CPI scratch plan and never become persistent pointers or dynamic account state.
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

/-- wf → payload length ≤ Memo.Ascii.maxBytes (512). -/
theorem wf_bounded (value : String) (h : wellFormed value = true) :
    value.length ≤ maxBytes := by
  unfold wellFormed ProofForge.Svm.Memo.Ascii.wellFormed at h
  simp at h
  unfold maxBytes
  exact h.1

/-- The public Memo budget is pinned to the extractor's 512-byte ceiling. -/
theorem maxBytes_eq : maxBytes = 512 := rfl

/-- Numeric form of `wf_bounded` for callers that do not unfold the budget constant. -/
theorem wf_bounded_512 (value : String) (h : wellFormed value = true) :
    value.length ≤ 512 := by
  have hb := wf_bounded value h
  unfold maxBytes ProofForge.Svm.Memo.Ascii.maxBytes at hb
  exact hb

end Ascii

namespace Utf8

def maxBytes : Nat := ProofForge.Svm.Memo.Utf8.maxBytes

def wellFormed (value : String) : Bool :=
  ProofForge.Svm.Memo.Utf8.wellFormed value

def bytesWellFormed (bytes : ByteArray) : Bool :=
  ProofForge.Svm.Memo.Utf8.bytesWellFormed bytes

/-- Write one compile-time UTF-8 Memo payload under the same fixed CPI geometry as `Ascii.write`.
Extraction accepts the payload when `wellFormed` holds (≤ 512 UTF-8 bytes, strict scan). -/
@[pf_inline] def write (value : String) : UInt64 :=
  ProofForge.Svm.Runtime.invoke 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.ascii value]

theorem maxBytes_eq : maxBytes = 512 := rfl

theorem maxBytes_eq_ascii : maxBytes = Ascii.maxBytes := rfl

end Utf8

/-- Compatibility spelling for the original fixed payload. New applications should select their
own static payload through `Ascii.write` or `Utf8.write`. -/
@[pf_inline] def writeOk : UInt64 :=
  Ascii.write "ok"

/-- `writeOk` is only a compatibility delegate to the generic bounded ASCII writer. -/
theorem writeOk_def : writeOk = Ascii.write "ok" := rfl

end ProofForge.Svm.Sdk.Memo
