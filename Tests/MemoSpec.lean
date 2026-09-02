import Examples.Svm.Memo

namespace Tests.MemoSpec

open Examples.Svm.Memo
open ProofForge.Svm.Sdk

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard Memo.writeOk == 0
#guard Memo.Ascii.write "proof-forge" == 0

#guard
  match write (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedMemo
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedMemo == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedMemo with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=2" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "call write"

end Tests.MemoSpec
