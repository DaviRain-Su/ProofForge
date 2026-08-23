import Projects.Phoenix
import ProofForge

namespace Tests.PhoenixSpec

open Projects.Phoenix
open ProofForge.Svm.Runtime
open Lean Elab Command

elab "#pf_guard_phoenix_artifact" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Projects.Phoenix none with
    | .ok program => pure program
    | .error reason => throwError reason
  match source.validateSvm with
  | .ok _ => pure ()
  | .error reason => throwError reason
  let program ←
    match ProofForge.Extract.IR.toLegacyProgram source with
    | .ok program => pure program
    | .error reason => throwError reason
  let asm ←
    match ProofForge.Svm.Emit.emitCounterAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.toUTF8.size < 450000 do
    throwError s!"Phoenix assembly budget exceeded: {asm.toUTF8.size} bytes"
  unless !asm.contains "\n\\\n" do
    throwError "Phoenix assembly contains a standalone backslash"
  let labels := (asm.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.endsWith ":" then some line else none
  unless labels.length == labels.eraseDups.length do
    let duplicates := labels.filter (fun label => 1 < labels.count label) |>.eraseDups
    throwError s!"Phoenix assembly contains duplicate labels: {duplicates}"
  unless ProofForge.Svm.ABI.dataLen program == 544 do
    throwError s!"Phoenix source account layout changed: {ProofForge.Svm.ABI.dataLen program} bytes"
  let some post := program.methods.find? (·.ixName == "postAsk")
    | throwError "missing postAsk"
  let some reduce := program.methods.find? (·.ixName == "reduceAsk")
    | throwError "missing reduceAsk"
  let some postBid := program.methods.find? (·.ixName == "postBid")
    | throwError "missing postBid"
  let some reduceBid := program.methods.find? (·.ixName == "reduceBid")
    | throwError "missing reduceBid"
  let some swap := program.methods.find? (·.ixName == "swapBuy")
    | throwError "missing swapBuy"
  let some swapSell := program.methods.find? (·.ixName == "swapSell")
    | throwError "missing swapSell"
  let some collect := program.methods.find? (·.ixName == "collectFees")
    | throwError "missing collectFees"
  unless post.paramCount == 5 && reduce.paramCount == 4 &&
      postBid.paramCount == 5 && reduceBid.paramCount == 4 &&
      swap.paramCount == 4 && swapSell.paramCount == 4 && collect.paramCount == 0 do
    throwError "Phoenix instruction parameter counts changed"
  unless asm.contains "; forBody 14" && asm.contains "; forBody 17" &&
      asm.contains "; forBody 4" do
    throwError "Phoenix bounded loops missing from assembly"

#pf_guard_phoenix_artifact

private def sameBusinessResult :
    Except Error (Projects.Phoenix.State × UInt64) →
      Except Error (Projects.Phoenix.State × UInt64) → Bool
  | .error a, .error b => a == b
  | .ok (a, ar), .ok (b, br) =>
      ar == br && a.sizes == b.sizes &&
        a.quoteLocked == b.quoteLocked && a.quoteFree == b.quoteFree &&
        a.baseLocked == b.baseLocked && a.baseFree == b.baseFree &&
        a.unclaimedFees == b.unclaimedFees && a.collectedFees == b.collectedFees
  | _, _ => false

private def sameSellResult :
    Except Error (Projects.Phoenix.State × UInt64) →
      Except Error (Projects.Phoenix.State × UInt64) → Bool
  | .error a, .error b => a == b
  | .ok (a, ar), .ok (b, br) =>
      ar == br && a.bidSizes == b.bidSizes &&
        a.quoteLocked == b.quoteLocked && a.quoteFree == b.quoteFree &&
        a.baseLocked == b.baseLocked && a.baseFree == b.baseFree &&
        a.unclaimedFees == b.unclaimedFees && a.collectedFees == b.collectedFees
  | _, _ => false

private def matchingSamples : List Projects.Phoenix.State := [
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
        (swapBuy s u64Max 0 want.toUInt64 limit.toUInt64)

private def sellSamples : List Projects.Phoenix.State := [
  { (init 1) with
    bidSizes := #v[2, 3, 1, 0], bidPriceTicks := #v[12, 11, 10, 0],
    quoteLocked := 67, baseFree := 6 },
  { (init 2) with
    bidSizes := #v[0, 2, 0, 1], bidPriceTicks := #v[0, 13, 0, 10],
    quoteLocked := 72, baseFree := 3, takerFeeBps := 25 },
  { (init 2) with
    baseLotsPerBaseUnit := 2,
    bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[4, 3, 2, 1],
    quoteLocked := 10, baseFree := 4 }
]

#guard sellSamples.all fun s =>
  (List.range 7).all fun want =>
    (List.range 15).all fun limit =>
      sameSellResult
        (swapSellAt s want.toUInt64 limit.toUInt64 0 0)
        (swapSell s u64Max 0 want.toUInt64 limit.toUInt64)

#guard (init 100).tickSize == 100
#guard (init 100).sequence == 1
#guard (init 100).takerFeeBps == 5
#guard (init 100).sizes[0]! == 0
#guard (init 100).priceTicks[0]! == 0
#guard (init 100).bidPriceTicks[0]! == 0
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
#guard orderedBids { (init 1) with
  bidSizes := #v[1, 1, 1, 0], bidPriceTicks := #v[11, 10, 10, 0],
  bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), ~~~(3 : UInt64), 0] }
#guard !orderedBids { (init 1) with
  bidSizes := #v[1, 0, 1, 0], bidPriceTicks := #v[10, 0, 11, 0],
  bidSequences := #v[~~~(1 : UInt64), 0, ~~~(2 : UInt64), 0] }
#guard Side.ask != Side.bid
#guard SelfTradeBehavior.abort != SelfTradeBehavior.cancelProvide

#guard
  match postAskAt { (init 100) with baseFree := 8 } 7 50 8 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && st.priceTicks[0]! == 50 && st.traders[0]! == 7 &&
        st.sequences[0]! == 1 && st.sequence == 2 &&
        st.baseLocked == 8 && st.baseFree == 0 && ret == 8
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with
        sizes := #v[3, 0, 0, 0], priceTicks := #v[60, 0, 0, 0],
        sequences := #v[1, 0, 0, 0], traders := #v[1, 0, 0, 0],
        sequence := 2, baseLocked := 3, baseFree := 5 }
      2 50 5 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[5, 3, 0, 0] && st.priceTicks == #v[50, 60, 0, 0] &&
        st.traders == #v[2, 1, 0, 0] && st.sequences == #v[2, 1, 0, 0] &&
        st.sequence == 3 && st.baseLocked == 8 && st.baseFree == 0 && ret == 5
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with
        sizes := #v[1, 1, 1, 1], priceTicks := #v[10, 20, 30, 40],
        sequences := #v[1, 2, 3, 4], sequence := 5,
        baseLocked := 4, baseFree := 1 }
      9 50 1 0 0 0 0 with
  | .error .overflow => true
  | _ => false

#guard
  match postAskFull { (init 100) with baseFree := 8 } 50 8 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && st.priceTicks[0]! == 50 &&
        st.sequences[0]! == 1 && st.sequence == 2 &&
        st.baseLocked == 8 && st.baseFree == 0 && ret == 8
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with
        sizes := #v[1, 0, 1, 1], priceTicks := #v[10, 0, 30, 40],
        sequences := #v[1, 0, 3, 4], traders := #v[1, 0, 3, 4],
        sequence := 5, baseLocked := 3, baseFree := 1 }
      2 20 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[1, 1, 1, 1] && st.priceTicks == #v[10, 20, 30, 40] &&
        st.traders == #v[1, 2, 3, 4] && st.sequences == #v[1, 5, 3, 4] &&
        orderedAsks st && ret == 1
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with
        sizes := #v[1, 2, 3, 4], priceTicks := #v[10, 20, 30, 40],
        sequences := #v[1, 2, 3, 4], traders := #v[1, 2, 3, 4],
        sequence := 5, baseLocked := 10, baseFree := 1 }
      9 15 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[1, 1, 2, 3] && st.priceTicks == #v[10, 15, 20, 30] &&
        st.traders == #v[1, 9, 2, 3] && st.sequences == #v[1, 5, 2, 3] &&
        st.baseLocked == 7 && st.baseFree == 4 && orderedAsks st && ret == 1
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with baseFree := 8 }
      7 50 8 9 0 10 0 with
  | .ok (st, ret) => st == { (init 100) with baseFree := 8 } && ret == 0
  | .error _ => false

#guard
  match postBidAt { (init 1) with quoteFree := 100 } 7 50 2 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[2, 0, 0, 0] && st.bidPriceTicks == #v[50, 0, 0, 0] &&
        st.bidTraders[0]! == 7 && st.bidSequences[0]! == ~~~(1 : UInt64) &&
        st.sequence == 2 && st.quoteLocked == 100 && st.quoteFree == 0 && ret == 2
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with
        bidSizes := #v[1, 1, 0, 0], bidPriceTicks := #v[50, 40, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        sequence := 3, quoteLocked := 90, quoteFree := 60 }
      9 60 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 1, 1, 0] && st.bidPriceTicks == #v[60, 50, 40, 0] &&
        st.bidSequences == #v[~~~(3 : UInt64), ~~~(1 : UInt64), ~~~(2 : UInt64), 0] &&
        st.quoteLocked == 150 && st.quoteFree == 0 && orderedBids st && ret == 1
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with
        bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[40, 30, 20, 10],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64),
          ~~~(3 : UInt64), ~~~(4 : UInt64)],
        sequence := 5, quoteLocked := 100, quoteFree := 100 }
      9 25 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 1, 1, 1] && st.bidPriceTicks == #v[40, 30, 25, 20] &&
        st.quoteLocked == 115 && st.quoteFree == 85 && orderedBids st && ret == 1
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with
        bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[40, 30, 20, 10],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64),
          ~~~(3 : UInt64), ~~~(4 : UInt64)],
        sequence := 5, quoteLocked := 100, quoteFree := 100 }
      9 10 1 0 0 0 0 with
  | .error .overflow => true
  | _ => false

#guard
  match postBidAt { (init 1) with quoteFree := 100 } 7 50 2 9 0 10 0 with
  | .ok (st, ret) => st == { (init 1) with quoteFree := 100 } && ret == 0
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
      u64Max 0 4 11 with
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
      u64Max 0 1 10 with
  | .ok (st, ret) => st.sizes[0]! == 2 && ret == 0
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        baseLocked := 2 }
      u64Max 0 0 10 with
  | .ok (st, ret) =>
      st.sizes[0]! == 2 && st.baseLocked == 2 && st.baseFree == 0 &&
        st.matchStopped == 1 && ret == 0
  | .error _ => false

#guard
  match swapBuyForAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        traders := #v[7, 8, 0, 0], quoteLocked := 1000, baseLocked := 5 }
      7 2 11 0 0 .abort with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuyForAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        traders := #v[7, 8, 0, 0], quoteLocked := 1000, baseLocked := 5 }
      7 2 11 0 0 .cancelProvide with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 977 && st.quoteFree == 22 &&
        st.baseLocked == 1 && st.baseFree == 4 && st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapBuyForAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        traders := #v[7, 8, 0, 0], quoteLocked := 1000, baseLocked := 5 }
      7 1 11 0 0 .decrementTake with
  | .ok (st, ret) =>
      st.sizes == #v[1, 3, 0, 0] && ret == 0 &&
        st.quoteLocked == 1000 && st.quoteFree == 0 &&
        st.baseLocked == 4 && st.baseFree == 1 && st.unclaimedFees == 0
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        traders := #v[7, 8, 0, 0], quoteLocked := 1000, baseLocked := 5 }
      7 1 2 11 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.baseLocked == 1 && st.baseFree == 4 && st.unclaimedFees == 1
  | .error _ => false

#guard
  let s :=
    { (init 1) with
      sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
      traders := #v[7, 8, 0, 0], quoteLocked := 1000, baseLocked := 5 }
  sameBusinessResult
    (swapBuyForAt s 7 1 11 0 0 .decrementTake)
    (swapBuy s 7 2 1 11)

#guard
  match swapSellAt
      { (init 1) with
        bidSizes := #v[2, 3, 5, 0], bidPriceTicks := #v[12, 11, 10, 0],
        quoteLocked := 107, baseFree := 4 }
      4 11 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 61 && st.quoteFree == 45 && st.baseFree == 4 &&
        st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapSellAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidLastSlots := #v[9, 0, 0, 0], quoteLocked := 57, baseFree := 2 }
      2 11 10 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 11 && st.quoteFree == 45 && st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapSellAt
      { (init 1) with
        bidSizes := #v[2, 0, 0, 0], bidPriceTicks := #v[10, 0, 0, 0],
        quoteLocked := 20, baseFree := 1 }
      1 11 0 0 with
  | .ok (st, ret) => st.bidSizes[0]! == 2 && st.quoteLocked == 20 && ret == 0
  | .error _ => false

#guard
  match swapSellForAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57, baseFree := 2 }
      7 2 11 0 0 .abort with
  | .error .overflow => true
  | _ => false

#guard
  match swapSellForAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57, baseFree := 2 }
      7 2 11 0 0 .cancelProvide with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 11 && st.quoteFree == 45 && st.unclaimedFees == 1
  | .error _ => false

#guard
  match swapSellForAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57, baseFree := 1 }
      7 1 11 0 0 .decrementTake with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 3, 0, 0] && ret == 0 &&
        st.quoteLocked == 45 && st.quoteFree == 12 && st.baseFree == 1 &&
        st.unclaimedFees == 0
  | .error _ => false

#guard
  let s :=
    { (init 1) with
      bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
      bidTraders := #v[7, 8, 0, 0], quoteLocked := 57, baseFree := 2 }
  sameSellResult
    (swapSellForAt s 7 2 11 0 0 .cancelProvide)
    (swapSell s 7 1 2 11)

#guard
  match sweepAsk { (init 100) with
      sizes := #v[2, 8, 0, 0], baseLocked := 10, baseFree := 0 } with
  | .ok (st, ret) =>
      st.sizes[0]! == 0 && st.sizes[1]! == 8 && st.baseLocked == 8 &&
        st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match reduceAsk
      { (init 100) with
        sizes := #v[8, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[7, 8, 0, 0],
        baseLocked := 9, baseFree := 1 }
      7 10 1 3 with
  | .ok (st, ret) =>
      st.sizes == #v[5, 1, 0, 0] && st.baseLocked == 6 && st.baseFree == 4 &&
        st.matchFilled == 0 && ret == 3
  | .error _ => false

#guard
  match reduceAsk
      { (init 100) with
        sizes := #v[2, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[7, 8, 0, 0],
        baseLocked := 3 }
      7 10 1 9 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && st.baseLocked == 1 && st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match reduceAsk
      { (init 100) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        sequences := #v[1, 0, 0, 0], traders := #v[7, 0, 0, 0], baseLocked := 2 }
      8 10 1 1 with
  | .error .overflow => true
  | _ => false

#guard
  match reduceBid
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57 }
      8 11 (~~~(2 : UInt64)) 2 with
  | .ok (st, ret) =>
      st.bidSizes == #v[2, 1, 0, 0] && st.quoteLocked == 35 &&
        st.quoteFree == 22 && ret == 2
  | .error _ => false

#guard
  match cancelBid
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57 }
      7 12 (~~~(1 : UInt64)) with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 3, 0, 0] && st.quoteLocked == 33 &&
        st.quoteFree == 24 && ret == 2
  | .error _ => false

#guard
  match reduceBid
      { (init 1) with
        bidSizes := #v[2, 0, 0, 0], bidPriceTicks := #v[12, 0, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), 0, 0, 0],
        bidTraders := #v[7, 0, 0, 0], quoteLocked := 24 }
      8 12 (~~~(1 : UInt64)) 1 with
  | .error .overflow => true
  | _ => false

#guard
  match cancelAsk { (init 100) with
      sizes := #v[8, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
      sequences := #v[1, 2, 0, 0], traders := #v[7, 8, 0, 0],
      baseLocked := 9 } 7 10 1 with
  | .ok (st, ret) => st.sizes[0]! == 0 && st.sizes[1]! == 1 &&
      st.baseLocked == 1 && st.baseFree == 8 && ret == 8
  | .error _ => false

#guard
  match cancelAsk (init 100) 7 10 1 with
  | .ok (st, ret) => st == init 100 && ret == 0
  | .error _ => false

#guard
  match collectFees { (init 100) with collectedFees := 9, unclaimedFees := 3 } with
  | .ok (st, ret) => st.collectedFees == 12 && st.unclaimedFees == 0 && ret == 3
  | .error _ => false

#guard
  match collectFees { (init 100) with collectedFees := u64Max, unclaimedFees := 1 } with
  | .error .overflow => true
  | _ => false

#guard bestAsk { (init 100) with
  sizes := #v[0, 0, 2, 1], priceTicks := #v[0, 0, 30, 40] } == 30
#guard bestBid { (init 100) with
  bidSizes := #v[0, 0, 2, 1], bidPriceTicks := #v[0, 0, 30, 20] } == 30
#guard bidQty { (init 100) with bidSizes := #v[1, 2, 3, 4] } == 10

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

#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedPhoenix == 344

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPhoenix with
  | .ok asm => asm.contains "err_swapBuy:"
  | .error _ => false

end Tests.PhoenixSpec
