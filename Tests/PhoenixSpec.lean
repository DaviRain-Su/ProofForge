import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Runtime

#guard (init 100).askPrice == 100
#guard (init 100).sizes[0]! == 0
#guard bestAsk (init 100) == 100
#guard askQty (init 100) == 0
#guard
  askQty { askPrice := 100, sizes := #v[1, 2, 3, 4], baseFree := 0 } == 10
#guard level0 (init 100) == 0
#guard feeOf 10000 == 5

#guard
  match postAsk (init 100) 8 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && ret == 8 && st.askPrice == 100 && st.sizes[1]! == 0
  | .error _ => false

#guard
  match postAsk { askPrice := 100, sizes := #v[3, 0, 0, 0], baseFree := 0 } 5 with
  | .ok (st, ret) => st.sizes[0]! == 3 && st.sizes[1]! == 5 && ret == 5
  | .error _ => false

#guard
  match postAsk { askPrice := 100, sizes := #v[1, 1, 1, 1], baseFree := 0 } 1 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy { askPrice := 100, sizes := #v[8, 0, 0, 0], baseFree := 1 } 3 with
  | .ok (st, ret) =>
      st.sizes[0]! == 5 && st.baseFree == 4 && ret == 3 && st.askPrice == 100
  | .error _ => false

#guard
  match swapBuy { askPrice := 100, sizes := #v[2, 8, 0, 0], baseFree := 0 } 3 with
  | .error .overflow => true
  | _ => false

#guard
  match sweepAsk { askPrice := 100, sizes := #v[2, 8, 0, 0], baseFree := 0 } with
  | .ok (st, ret) =>
      st.sizes[0]! == 0 && st.sizes[1]! == 8 && st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match swapBuy { askPrice := 100, sizes := #v[0, 8, 0, 0], baseFree := 0 } 3 with
  | .error .overflow => true
  | _ => false

#guard
  match reduceAsk { askPrice := 100, sizes := #v[8, 1, 0, 0], baseFree := 0 } 3 with
  | .ok (st, ret) => st.sizes[0]! == 5 && st.sizes[1]! == 1 && ret == 3
  | .error _ => false

#guard
  match reduceAsk { askPrice := 100, sizes := #v[2, 1, 0, 0], baseFree := 0 } 9 with
  | .error .overflow => true
  | _ => false

#guard
  match cancelAsk { askPrice := 100, sizes := #v[8, 1, 0, 0], baseFree := 0 } with
  | .ok (st, ret) => st.sizes[0]! == 0 && st.sizes[1]! == 1 && ret == 8
  | .error _ => false

#guard
  match cancelAsk (init 100) with
  | .error .overflow => true
  | _ => false

#guard checkLimit (init 100) 50 == false
#guard checkLimit (init 100) 100 == true
#guard checkTif 0 == true
#guard takeFee 10000 == 5

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedPhoenix
#guard ProofForge.IR.dataLen ProofForge.Golden.extractedPhoenix == 56

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "sizes_0" &&
        asm.contains "sizes_3"

end Tests.PhoenixSpec
