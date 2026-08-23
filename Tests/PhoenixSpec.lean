import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Runtime

#guard (init 100).tickSize == 100
#guard (init 100).sequence == 1
#guard (init 100).takerFeeBps == 5
#guard (init 100).sizes[0]! == 0
#guard (init 100).priceTicks[0]! == 0
#guard (init 100).baseLocked == 0
#guard (init 100).baseFree == 0
#guard bestAsk (init 100) == 0
#guard askQty (init 100) == 0
#guard nextSeq (init 100) == 1
#guard feeBpsOf (init 100) == 5
#guard makerBase (init 100) == 0
#guard takerBase (init 100) == 0
#guard feeOf 10000 == 5
#guard feeOfBps 10000 25 == 25
#guard Side.ask != Side.bid
#guard SelfTradeBehavior.abort != SelfTradeBehavior.cancelProvide

#guard
  match postAsk (init 100) 8 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && ret == 8 && st.sizes[1]! == 0
  | .error _ => false

#guard
  match postAsk { (init 100) with sizes := #v[3, 0, 0, 0] } 5 with
  | .ok (st, ret) => st.sizes[0]! == 3 && st.sizes[1]! == 5 && ret == 5
  | .error _ => false

#guard
  match postAsk { (init 100) with sizes := #v[1, 1, 1, 1] } 1 with
  | .error .overflow => true
  | _ => false

#guard
  match postAskFull (init 100) 50 8 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && st.priceTicks[0]! == 50 &&
        st.sequences[0]! == 1 && st.sequence == 2 && st.baseLocked == 8 && ret == 8
  | .error _ => false

#guard
  match swapBuyAt
      { (init 100) with sizes := #v[8, 0, 0, 0], baseFree := 1 }
      3 0 0 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 5 && st.baseFree == 4 && ret == 3
  | .error _ => false

#guard
  match swapBuyAt
      { (init 100) with sizes := #v[2, 8, 0, 0], baseFree := 0 }
      3 0 0 0 with
  | .ok (st, ret) => st.sizes[0]! == 0 && st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match swapBuyAt
      { (init 100) with sizes := #v[8, 0, 0, 0], priceTicks := #v[100, 0, 0, 0] }
      3 50 0 0 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuyAt
      { (init 100) with
        sizes := #v[8, 0, 0, 0], priceTicks := #v[100, 0, 0, 0],
        lastTimes := #v[10, 0, 0, 0] }
      3 100 0 10 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuyAt
      { (init 100) with
        sizes := #v[8, 0, 0, 0], priceTicks := #v[100, 0, 0, 0],
        lastSlots := #v[20, 0, 0, 0] }
      3 100 20 0 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuyAt
      { (init 100) with sizes := #v[8, 0, 0, 0], baseFree := u64Max }
      1 0 0 0 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy
      { (init 100) with
        sizes := #v[8, 0, 0, 0], priceTicks := #v[100, 0, 0, 0], baseFree := 1 }
      3 100 with
  | .ok (st, ret) => st.sizes[0]! == 5 && st.baseFree == 4 && ret == 3
  | .error _ => false

#guard
  match swapBuy
      { (init 100) with sizes := #v[8, 0, 0, 0], priceTicks := #v[100, 0, 0, 0] }
      3 99 with
  | .error .overflow => true
  | _ => false

#guard
  match sweepAsk { (init 100) with
      sizes := #v[2, 8, 0, 0], baseLocked := 10, baseFree := 0 } with
  | .ok (st, ret) =>
      st.sizes[0]! == 0 && st.sizes[1]! == 8 && st.baseLocked == 8 &&
        st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match reduceAsk { (init 100) with sizes := #v[8, 1, 0, 0] } 3 with
  | .ok (st, ret) => st.sizes[0]! == 5 && ret == 3
  | .error _ => false

#guard
  match reduceAsk { (init 100) with sizes := #v[2, 1, 0, 0] } 9 with
  | .error .overflow => true
  | _ => false

#guard
  match cancelAsk { (init 100) with
      sizes := #v[8, 1, 0, 0], baseLocked := 9 } with
  | .ok (st, ret) => st.sizes[0]! == 0 && st.sizes[1]! == 1 &&
      st.baseLocked == 1 && ret == 8
  | .error _ => false

#guard
  match cancelAsk (init 100) with
  | .error .overflow => true
  | _ => false

#guard checkLimit { (init 100) with priceTicks := #v[100, 0, 0, 0] } 50 == false
#guard checkLimit { (init 100) with priceTicks := #v[100, 0, 0, 0] } 100 == true
#guard checkTif 0 == true
#guard takeFee 10000 == 5
#guard expired 0 0 10 10 == false
#guard expired 5 0 10 10 == true
#guard expired 0 5 10 10 == true
#guard expired 10 0 10 0 == true
#guard expired 0 10 0 10 == true

#guard ProofForge.IR.dataLen ProofForge.Golden.extractedPhoenix == 280

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .ok asm => asm.contains "err_swapBuy:"
  | .error _ => false

end Tests.PhoenixSpec
