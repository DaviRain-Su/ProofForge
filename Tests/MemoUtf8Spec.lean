import Examples.MemoUtf8
import ProofForge

/-!
Focused geometry and extraction checks for svm-sdk-006 UTF-8 Memo.
-/

namespace Tests.MemoUtf8Spec

open ProofForge.Svm.Sdk

#guard Memo.Utf8.wellFormed "café"
#guard Memo.Utf8.wellFormed "λ"
#guard !Memo.Utf8.wellFormed (String.ofList (List.replicate 513 'a'))
#guard !Memo.Utf8.bytesWellFormed (ByteArray.mk #[0xc0, 0x80])
#guard Memo.Utf8.write "café" == 0

#pf_build Examples.MemoUtf8

end Tests.MemoUtf8Spec
