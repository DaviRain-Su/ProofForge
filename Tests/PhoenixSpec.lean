import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Runtime

private def sameBusinessResult :
    Except Error (State × UInt64) → Except Error (State × UInt64) → Bool
  | .error a, .error b => a == b
  | .ok (a, ar), .ok (b, br) =>
      ar == br && a.sizes == b.sizes &&
        a.quoteLocked == b.quoteLocked && a.quoteFree == b.quoteFree &&
        a.baseLocked == b.baseLocked && a.baseFree == b.baseFree &&
        a.unclaimedFees == b.unclaimedFees && a.collectedFees == b.collectedFees
  | _, _ => false

private def matchingSamples : List State := [
  { (init 1) with
    sizes := #v[2, 3, 1, 0], priceTicks := #v[10, 11, 12, 0],
    quoteLocked := 1000, baseLocked := 6 },
  { (init 2) with
    sizes := #v[0, 2, 0, 1], priceTicks := #v[0, 10, 0, 13],
    quoteLocked := 1000, baseLocked := 3, takerFeeBps := 25 },
  { (init 1) with
    sizes := #v[1, 1, 1, 1], priceTicks := #v[0, 1, 1, 2],
    quoteLocked := 1000, baseLocked := 4, baseLotsPerBaseUnit := 2 }
]

#guard matchingSamples.all fun s =>
  (List.range 9).all fun want =>
    (List.range 15).all fun limit =>
      sameBusinessResult
        (swapBuyAt s want.toUInt64 limit.toUInt64 0 0)
        (swapBuy s want.toUInt64 limit.toUInt64)

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
#guard feeOfBps 1 5 == 1
#guard ceilDiv 0 7 == 0
#guard ceilDiv 1 7 == 1
#guard canonicalAskTree.valid
#guard canonicalAskTree.inorderLevels == #v[0, 1, 2, 3]
#guard
  let badNode := { canonicalAskTree.nodes[0]! with left := 4 }
  let badTree := { canonicalAskTree with nodes := canonicalAskTree.nodes.set 0 badNode }
  !badTree.valid
#guard orderedAsks { (init 1) with
  sizes := #v[1, 1, 1, 0], priceTicks := #v[10, 10, 11, 0],
  sequences := #v[1, 2, 3, 0] }
#guard !orderedAsks { (init 1) with
  sizes := #v[1, 0, 1, 0], priceTicks := #v[11, 0, 10, 0],
  sequences := #v[1, 0, 2, 0] }
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
      { (init 1) with
        sizes := #v[2, 3, 5, 0], priceTicks := #v[10, 11, 12, 0],
        quoteLocked := 1000, baseLocked := 10 }
      4 11 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 957 && st.quoteFree == 42 &&
        st.baseLocked == 6 && st.baseFree == 4 &&
        st.unclaimedFees == 1 && st.collectedFees == 0
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        lastSlots := #v[9, 0, 0, 0], quoteLocked := 100, baseLocked := 5 }
      2 11 10 0 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 77 && st.quoteFree == 22 &&
        st.baseLocked == 1 && st.baseFree == 4 && st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        lastSlots := #v[10, 0, 0, 0], lastTimes := #v[10, 0, 0, 0],
        quoteLocked := 100, baseLocked := 2 }
      1 10 10 10 with
  | .ok (st, ret) => st.sizes[0]! == 1 && ret == 1 && st.baseFree == 1
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        lastSlots := #v[10, 0, 0, 0], quoteLocked := 100, baseLocked := 2 }
      1 10 11 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 0 && ret == 0 && st.baseLocked == 0 && st.baseFree == 2
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[11, 0, 0, 0],
        quoteLocked := 100, baseLocked := 2 }
      1 10 0 0 with
  | .ok (st, ret) => st.sizes[0]! == 2 && ret == 0 && st.quoteLocked == 100
  | .error _ => false

#guard
  match swapBuyAt (init 1) 4 10 0 0 with
  | .ok (st, ret) => st.sizes == empty4 && ret == 0
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        lastSlots := #v[10, 0, 0, 0], baseLocked := 2 }
      0 10 11 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 2 && st.baseLocked == 2 && st.baseFree == 0 && ret == 0
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[1, 0, 0, 0], baseLocked := 1,
        quoteLocked := 2, baseFree := u64Max }
      1 0 0 0 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 3, 5, 0], priceTicks := #v[10, 11, 12, 0],
        quoteLocked := 1000, baseLocked := 10 }
      4 11 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 957 && st.quoteFree == 42 &&
        st.baseLocked == 6 && st.baseFree == 4 && st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[11, 0, 0, 0],
        quoteLocked := 100, baseLocked := 2 }
      1 10 with
  | .ok (st, ret) => st.sizes[0]! == 2 && ret == 0
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        baseLocked := 2 }
      0 10 with
  | .ok (st, ret) =>
      st.sizes[0]! == 2 && st.baseLocked == 2 && st.baseFree == 0 &&
        st.matchStopped == 1 && ret == 0
  | .error _ => false

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
#guard expired 10 0 10 0 == false
#guard expired 0 10 0 10 == false
#guard expired 10 0 11 0 == true
#guard expired 0 10 0 11 == true

#guard ProofForge.IR.dataLen ProofForge.Golden.extractedPhoenix == 344

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .ok asm => asm.contains "err_swapBuy:"
  | .error _ => false

end Tests.PhoenixSpec
