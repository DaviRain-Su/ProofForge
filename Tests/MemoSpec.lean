import Examples.Memo

namespace Tests.MemoSpec

open Examples.Memo
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard memoWrite == 0

#guard
  match write (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedMemo
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedMemo == 2

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedMemo with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=1" &&
        asm.contains "dataLen=2" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 2" &&
        asm.contains "ja write"

end Tests.MemoSpec
