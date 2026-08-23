import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Runtime

#guard (init 100).askPrice == 100
#guard (init 100).sizes[0]! == 0
#guard (init 100).sizes[1]! == 0
#guard bestAsk (init 100) == 100
#guard askQty (init 100) == 0
#guard level0 (init 100) == 0

#guard
  match postAsk (init 100) 8 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && ret == 8 && st.askPrice == 100 && st.sizes[1]! == 0
  | .error _ => false

#guard
  match postAsk { askPrice := 100, sizes := #v[3, 0, 0, 0], baseFree := 0 } 1 with
  | .error .overflow => true
  | _ => false

#guard
  match postAsk1 (init 100) 5 with
  | .ok (st, ret) => st.sizes[1]! == 5 && ret == 5 && st.sizes[0]! == 0
  | .error _ => false

#guard
  match swapBuy { askPrice := 100, sizes := #v[8, 0, 0, 0], baseFree := 1 } 3 with
  | .ok (st, ret) =>
      st.sizes[0]! == 5 && st.baseFree == 4 && ret == 3 && st.askPrice == 100
  | .error _ => false

#guard
  match swapBuy { askPrice := 100, sizes := #v[2, 0, 0, 0], baseFree := 0 } 3 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy1 { askPrice := 100, sizes := #v[0, 8, 0, 0], baseFree := 0 } 3 with
  | .ok (st, ret) => st.sizes[1]! == 5 && st.baseFree == 3 && ret == 3
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedPhoenix
#guard ProofForge.IR.dataLen ProofForge.Golden.extractedPhoenix == 56

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "sizes_0" &&
        asm.contains "sizes_1"

end Tests.PhoenixSpec
