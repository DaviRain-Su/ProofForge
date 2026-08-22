import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Runtime

#guard (init 100).askPrice == 100
#guard (init 100).askSize == 0
#guard bestAsk (init 100) == 100
#guard askQty (init 100) == 0

#guard
  match postAsk (init 100) 8 with
  | .ok (st, ret) => st.askSize == 8 && ret == 8 && st.askPrice == 100
  | .error _ => false

#guard
  match postAsk { askPrice := 100, askSize := 3, baseFree := 0 } 1 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy { askPrice := 100, askSize := 8, baseFree := 1 } 3 with
  | .ok (st, ret) =>
      st.askSize == 5 && st.baseFree == 4 && ret == 3 && st.askPrice == 100
  | .error _ => false

#guard
  match swapBuy { askPrice := 100, askSize := 2, baseFree := 0 } 3 with
  | .error .overflow => true
  | _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedPhoenix

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "askPrice"

end Tests.PhoenixSpec
