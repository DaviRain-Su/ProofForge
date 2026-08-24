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
  unless source.schema.leaves.any (·.name == "lastEvent_tag") &&
      source.schema.leaves.any (·.name == "lastEvent_p8") &&
      source.schema.leaves.any (·.name == "events_0_tag") &&
      source.schema.leaves.any (·.name == "events_4_p8") &&
      source.schema.leaves.any (·.name == "traderKey3_3") &&
      source.schema.leaves.any (·.name == "traderBaseFree_3") &&
      source.schema.leaves.any (·.name == "eventCount") do
    throwError "Phoenix bounded event/trader layout is missing"
  let some initMethod := source.methods.find? (·.ixName == "initialize")
    | throwError "missing initialize"
  let initValues := initMethod.ops.filterMap fun
    | .returnState value => some value
    | _ => none
  unless initValues.size == source.schema.leaves.size do
    throwError s!"Phoenix init covers {initValues.size}/{source.schema.leaves.size} state leaves"
  for (name, expected) in #[
      ("traderCount", .lit 0), ("traderBumpIndex", .lit 1), ("traderFreeHead", .lit 1)
    ] do
    let some index := source.schema.leaves.findIdx? (·.name == name)
      | throwError s!"missing init leaf {name}"
    unless initValues[index]! == expected do
      throwError s!"Phoenix init value for {name} is {repr initValues[index]!}"
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let asm ←
    match ProofForge.Svm.Emit.emitProgramAsm source with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.toUTF8.size < 5750000 do
    throwError s!"Phoenix assembly budget exceeded: {asm.toUTF8.size} bytes"
  unless !asm.contains "\n\\\n" do
    throwError "Phoenix assembly contains a standalone backslash"
  let labels := (asm.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.endsWith ":" then some line else none
  unless labels.length == labels.eraseDups.length do
    let duplicates := labels.filter (fun label => 1 < labels.count label) |>.eraseDups
    throwError s!"Phoenix assembly contains duplicate labels: {duplicates}"
  unless ProofForge.Svm.IR.dataLen program == 1376 do
    throwError s!"Phoenix source account layout changed: {ProofForge.Svm.IR.dataLen program} bytes"
  unless ProofForge.Svm.IR.cpiAccountCount program == 11 do
    throwError s!"Phoenix CPI account scan stopped early: " ++
      s!"{ProofForge.Svm.IR.cpiAccountCount program}/11 accounts"
  let some deposit := program.methods.find? (·.ixName == "depositFunds")
    | throwError "missing depositFunds"
  let some initProgram := program.methods.find? (·.ixName == "initialize")
    | throwError "missing SVM initialize"
  let some withdrawBase := program.methods.find? (·.ixName == "withdrawBase")
    | throwError "missing withdrawBase"
  let some withdrawQuote := program.methods.find? (·.ixName == "withdrawQuote")
    | throwError "missing withdrawQuote"
  let some evictSeat := program.methods.find? (·.ixName == "evictSeat")
    | throwError "missing evictSeat"
  let some traderIndex := program.methods.find? (·.ixName == "traderIndexOf")
    | throwError "missing traderIndexOf"
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
  let some eventKind := program.methods.find? (·.ixName == "lastEventKind")
    | throwError "missing lastEventKind"
  let some eventAmount := program.methods.find? (·.ixName == "lastEventAmount")
    | throwError "missing lastEventAmount"
  let some eventCount := program.methods.find? (·.ixName == "eventCountOf")
    | throwError "missing eventCountOf"
  let rec hasIndexSet
      (fuel : Nat) (field : String) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .indexSet name _ _ _ _ => name == field
        | .ite _ _ _ thn els =>
            hasIndexSet fuel' field thn || hasIndexSet fuel' field els
        | .forBody _ body => hasIndexSet fuel' field body
        | _ => false
  let rec countIndexSets
      (fuel : Nat) (field : String) (ops : Array ProofForge.Svm.IR.Op) : Nat :=
    match fuel with
    | 0 => 0
    | fuel' + 1 => ops.foldl (init := 0) fun count op =>
        count + match op with
        | .indexSet name _ _ _ _ => if name == field then 1 else 0
        | .ite _ _ _ thn els =>
            countIndexSets fuel' field thn + countIndexSets fuel' field els
        | .forBody _ body => countIndexSets fuel' field body
        | _ => 0
  let rec hasIndexSetAt
      (fuel : Nat) (field : String) (byteOffset : Nat)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .indexSet name _ _ _ offset => name == field && offset == byteOffset
        | .ite _ _ _ thn els =>
            hasIndexSetAt fuel' field byteOffset thn ||
              hasIndexSetAt fuel' field byteOffset els
        | .forBody _ body => hasIndexSetAt fuel' field byteOffset body
        | _ => false
  let rec hasIndexSetValue
      (fuel : Nat) (field : String) (value : ProofForge.Svm.Ops.Val)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .indexSet name _ actual _ _ => name == field && actual == value
        | .ite _ _ _ thn els =>
            hasIndexSetValue fuel' field value thn || hasIndexSetValue fuel' field value els
        | .forBody _ body => hasIndexSetValue fuel' field value body
        | _ => false
  let rec hasStoreField
      (fuel : Nat) (field : String) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .storeField name _ => name == field
        | .ite _ _ _ thn els =>
            hasStoreField fuel' field thn || hasStoreField fuel' field els
        | .forBody _ body => hasStoreField fuel' field body
        | _ => false
  let rec hasStoreFieldValue
      (fuel : Nat) (field : String) (value : ProofForge.Svm.Ops.Val)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .storeField name actual => name == field && actual == value
        | .ite _ _ _ thn els =>
            hasStoreFieldValue fuel' field value thn ||
              hasStoreFieldValue fuel' field value els
        | .forBody _ body => hasStoreFieldValue fuel' field value body
        | _ => false
  let rec hasOkStateValue
      (fuel : Nat) (value : ProofForge.Svm.Ops.Val)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .okState actual => actual == value
        | .ite _ _ _ thn els =>
            hasOkStateValue fuel' value thn || hasOkStateValue fuel' value els
        | .forBody _ body => hasOkStateValue fuel' value body
        | _ => false
  let rec hasTransferRecipe
      (fuel programIx sourceIx mintIx destinationIx authorityIx : Nat)
      (seeds : Array ProofForge.Svm.Ops.PdaSeed) (signed : Bool)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .invoke actualProgram metas data actualSeeds bump =>
            actualProgram == programIx &&
              metas == #[
                { acc := sourceIx, signer := false, writable := true },
                { acc := mintIx, signer := false, writable := false },
                { acc := destinationIx, signer := false, writable := true },
                { acc := authorityIx, signer := true, writable := false }] &&
              (match data with
               | #[.u8le (.lit 12), .u64le _, .u8le (.lit 6)] => true
               | _ => false) &&
              actualSeeds == seeds && bump.isSome == signed
        | .ite _ _ _ thn els =>
            hasTransferRecipe fuel' programIx sourceIx mintIx destinationIx authorityIx
                seeds signed thn ||
              hasTransferRecipe fuel' programIx sourceIx mintIx destinationIx authorityIx
                seeds signed els
        | .forBody _ body =>
            hasTransferRecipe fuel' programIx sourceIx mintIx destinationIx authorityIx
              seeds signed body
        | _ => false
  let rec hasPhoenixRecord
      (fuel : Nat) (origin totalEvents : UInt64) (eventTag : Option UInt64)
      (ops : Array ProofForge.Svm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun
        | .invoke programIx metas data seeds bump =>
            let header :=
              programIx == 8 &&
                metas == #[{ acc := 9, signer := true, writable := false }] &&
                seeds == #[.ascii "log"] &&
                bump == some (ProofForge.Svm.Ops.findPda "log") &&
                data[0]? == some (.selfEntry 15 "log") &&
                data[1]? == some (.u8le (.lit 1)) &&
                data[2]? == some (.u8le (.lit origin)) &&
                (match data[3]? with
                 | some (ProofForge.Svm.Ops.CpiWord.u64le _) => true
                 | _ => false) &&
                data[4]? == some (ProofForge.Svm.Ops.CpiWord.u64le ProofForge.Svm.Ops.unixTime) &&
                data[5]? == some (ProofForge.Svm.Ops.CpiWord.u64le ProofForge.Svm.Ops.clockSlot) &&
                data[6]? == some (ProofForge.Svm.Ops.CpiWord.u64le
                  (ProofForge.Svm.Ops.accKeyWord 0 0)) &&
                data[7]? == some (ProofForge.Svm.Ops.CpiWord.u64le
                  (ProofForge.Svm.Ops.accKeyWord 0 1)) &&
                data[8]? == some (ProofForge.Svm.Ops.CpiWord.u64le
                  (ProofForge.Svm.Ops.accKeyWord 0 2)) &&
                data[9]? == some (ProofForge.Svm.Ops.CpiWord.u64le
                  (ProofForge.Svm.Ops.accKeyWord 0 3)) &&
                data[10]? == some (.accKey 0) &&
                data[11]? == some (.u16le (.lit totalEvents))
            header && match eventTag with
              | none => data.size == 12
              | some tag =>
                  14 < data.size && data[12]? == some (.u8le (.lit tag)) &&
                    data[13]? == some (.u16le (.lit 0))
        | .ite _ _ _ thn els =>
            hasPhoenixRecord fuel' origin totalEvents eventTag thn ||
              hasPhoenixRecord fuel' origin totalEvents eventTag els
        | .forBody _ body => hasPhoenixRecord fuel' origin totalEvents eventTag body
        | _ => false
  let baseVaultSeeds : Array ProofForge.Svm.Ops.PdaSeed :=
    #[.ascii "vault", .stateKey, .accKey 3]
  let quoteVaultSeeds : Array ProofForge.Svm.Ops.PdaSeed :=
    #[.ascii "vault", .stateKey, .accKey 4]
  unless hasTransferRecipe 32 7 1 3 5 0 #[] false deposit.ops &&
      hasTransferRecipe 32 7 2 4 6 0 #[] false deposit.ops &&
      hasTransferRecipe 32 7 5 3 1 5 baseVaultSeeds true withdrawBase.ops &&
      hasTransferRecipe 32 7 6 4 2 6 quoteVaultSeeds true withdrawQuote.ops &&
      hasTransferRecipe 32 7 2 4 6 0 #[] false swap.ops &&
      hasTransferRecipe 32 7 5 3 1 5 baseVaultSeeds true swap.ops &&
      hasTransferRecipe 32 7 1 3 5 0 #[] false swapSell.ops &&
      hasTransferRecipe 32 7 6 4 2 6 quoteVaultSeeds true swapSell.ops do
    throwError s!"Phoenix dual-vault TransferChecked recipes are incomplete: " ++
      s!"depositBase={hasTransferRecipe 32 7 1 3 5 0 #[] false deposit.ops}, " ++
      s!"depositQuote={hasTransferRecipe 32 7 2 4 6 0 #[] false deposit.ops}, " ++
      s!"withdrawBase={hasTransferRecipe 32 7 5 3 1 5 baseVaultSeeds true withdrawBase.ops}, " ++
      s!"withdrawQuote={hasTransferRecipe 32 7 6 4 2 6 quoteVaultSeeds true withdrawQuote.ops}, " ++
      s!"swapBuyIn={hasTransferRecipe 32 7 2 4 6 0 #[] false swap.ops}, " ++
      s!"swapBuyOut={hasTransferRecipe 32 7 5 3 1 5 baseVaultSeeds true swap.ops}, " ++
      s!"swapSellIn={hasTransferRecipe 32 7 1 3 5 0 #[] false swapSell.ops}, " ++
      s!"swapSellOut={hasTransferRecipe 32 7 6 4 2 6 quoteVaultSeeds true swapSell.ops}"
  match ProofForge.Svm.IR.rawSelfEntry? program with
  | .ok (some entry) =>
      unless entry.tag == 15 && entry.authoritySeed == "log" do
        throwError s!"Phoenix raw log entry changed: {repr entry}"
  | result => throwError s!"Phoenix raw log entry is missing: {repr result}"
  unless hasPhoenixRecord 32 100 0 none initProgram.ops &&
      hasPhoenixRecord 32 13 0 none deposit.ops &&
      hasPhoenixRecord 32 12 0 none withdrawBase.ops &&
      hasPhoenixRecord 32 12 0 none withdrawQuote.ops &&
      hasPhoenixRecord 32 106 0 none evictSeat.ops &&
      hasPhoenixRecord 32 3 0 none post.ops &&
      hasPhoenixRecord 32 3 1 (some 3) post.ops &&
      hasPhoenixRecord 32 3 1 (some 5) post.ops &&
      hasPhoenixRecord 32 3 1 (some 8) post.ops &&
      hasPhoenixRecord 32 3 0 none postBid.ops &&
      hasPhoenixRecord 32 3 1 (some 3) postBid.ops &&
      hasPhoenixRecord 32 3 1 (some 5) postBid.ops &&
      hasPhoenixRecord 32 3 1 (some 8) postBid.ops &&
      hasPhoenixRecord 32 5 0 none reduce.ops &&
      hasPhoenixRecord 32 5 1 (some 4) reduce.ops &&
      hasPhoenixRecord 32 5 0 none reduceBid.ops &&
      hasPhoenixRecord 32 5 1 (some 4) reduceBid.ops &&
      hasPhoenixRecord 32 0 1 (some 2) swap.ops &&
      hasPhoenixRecord 32 0 1 (some 4) swap.ops &&
      hasPhoenixRecord 32 0 1 (some 6) swap.ops &&
      hasPhoenixRecord 32 0 1 (some 9) swap.ops &&
      hasPhoenixRecord 32 0 1 (some 2) swapSell.ops &&
      hasPhoenixRecord 32 0 1 (some 4) swapSell.ops &&
      hasPhoenixRecord 32 0 1 (some 6) swapSell.ops &&
      hasPhoenixRecord 32 0 1 (some 9) swapSell.ops &&
      hasPhoenixRecord 32 108 1 (some 7) collect.ops do
    throwError "Phoenix AuditLogHeader/event Borsh records are incomplete"
  unless hasStoreField 32 "baseFree" withdrawBase.ops &&
      hasIndexSet 32 "traderBaseFree" withdrawBase.ops &&
      hasStoreField 32 "quoteFree" withdrawQuote.ops &&
      hasIndexSet 32 "traderQuoteFree" withdrawQuote.ops do
    throwError "Phoenix PDA withdrawals lost their state continuation"
  unless hasIndexSet 32 "traderBaseLocked" post.ops &&
      hasIndexSet 32 "traderBaseFree" post.ops &&
      hasIndexSet 32 "sequences" post.ops && hasStoreField 32 "sequence" post.ops &&
      hasIndexSet 32 "traderQuoteLocked" postBid.ops &&
      hasIndexSet 32 "traderQuoteFree" postBid.ops &&
      hasIndexSet 32 "bidSequences" postBid.ops && hasStoreField 32 "sequence" postBid.ops do
    throwError "Phoenix post entries do not preserve composed ledger/book updates"
  unless hasIndexSetValue 32 "traderBaseFree" (.arg 0) deposit.ops &&
      hasIndexSetValue 32 "traderQuoteFree" (.arg 1) deposit.ops do
    throwError "Phoenix state-loop parameters are not in source ABI order"
  unless hasStoreFieldValue 32 "lastEvent_p2" (.arg 2) post.ops &&
      hasStoreFieldValue 32 "lastEvent_p3" (.arg 3) post.ops &&
      hasStoreFieldValue 32 "lastEvent_p4" (.arg 0) post.ops &&
      hasStoreFieldValue 32 "lastEvent_p5" (.arg 1) post.ops &&
      hasOkStateValue 32 (.arg 1) post.ops do
    throwError "Phoenix nested bind parameters are not in source ABI order"
  unless hasIndexSet 32 "traderQuoteFree" swap.ops &&
      hasIndexSet 32 "traderBaseLocked" swap.ops &&
      hasIndexSet 32 "traderBaseFree" swap.ops &&
      hasIndexSet 32 "traderQuoteLocked" swapSell.ops &&
      hasIndexSet 32 "traderQuoteFree" swapSell.ops &&
      hasIndexSet 32 "traderBaseFree" swapSell.ops do
    throwError "Phoenix swap entries do not settle both maker and taker TraderState"
  unless hasIndexSetAt 32 "events" 72 swap.ops &&
      hasIndexSetAt 32 "events" 72 swapSell.ops do
    throwError "Phoenix swaps do not lower the widest MarketEvent payload leaf"
  unless countIndexSets 32 "traderQuoteLocked" reduceBid.ops == 1 &&
      countIndexSets 32 "traderQuoteFree" reduceBid.ops == 1 &&
      countIndexSets 32 "bidSizes" reduceBid.ops == 1 do
    throwError "Phoenix bid reduction replays a composed state transition"
  let feeSnapshots := collect.ops.filterMap fun
    | .letLocal localId (.field (.arg 0) "unclaimedFees") => some localId
    | _ => none
  unless hasStoreFieldValue 32 "unclaimedFees" (.lit 0) collect.ops &&
      feeSnapshots.any (fun localId =>
        hasIndexSetValue 32 "events" (.local localId) collect.ops &&
          hasOkStateValue 32 (.local localId) collect.ops) do
    throwError "Phoenix fee collection lost its pre-write scalar snapshot"
  unless deposit.paramCount == 2 && withdrawBase.paramCount == 1 &&
      withdrawQuote.paramCount == 1 && evictSeat.paramCount == 0 &&
      traderIndex.paramCount == 4 &&
      post.paramCount == 6 && reduce.paramCount == 3 &&
      postBid.paramCount == 6 && reduceBid.paramCount == 3 &&
      swap.paramCount == 5 && swapSell.paramCount == 5 && collect.paramCount == 0 &&
      eventKind.paramCount == 0 && eventAmount.paramCount == 0 && eventCount.paramCount == 0 do
    throwError "Phoenix instruction parameter counts changed"
  unless asm.contains "; CFG loop header bound=17" &&
      asm.contains "; CFG loop header bound=19" &&
      asm.contains "; CFG loop header bound=4" do
    throwError "Phoenix bounded loops missing from assembly"
  unless asm.contains "cfg_swapBuy_block_" && asm.contains "cfg_swapBuy_relay_" &&
      asm.contains "lddw r0, 0x1001" && !asm.contains "@@CFG_EDGE_" do
    throwError "Phoenix CFG layout or long-jump relays are incomplete"
  unless asm.contains "; checkPdaSeeds account=5 count=3" &&
      asm.contains "; checkPdaSeeds account=6 count=3" do
    throwError "Phoenix canonical vault checks are missing from assembly"

#pf_guard_phoenix_artifact

private def withSeats12 (s : Projects.Phoenix.State) : Projects.Phoenix.State :=
  { s with
    traderCount := 2
    traderBumpIndex := 3
    traderFreeHead := 3
    traderUsed := #v[1, 1, 0, 0]
    traderKey0 := #v[0, 22, 0, 0]
    traderKey1 := #v[0, 23, 0, 0]
    traderKey2 := #v[0, 24, 0, 0]
    traderKey3 := #v[0, 25, 0, 0] }

private def sameBusinessResult :
    Except Error (Projects.Phoenix.State × UInt64) →
      Except Error (Projects.Phoenix.State × UInt64) → Bool
  | .error a, .error b => a == b
  | .ok (a, ar), .ok (b, br) =>
      ar == br && a.sizes == b.sizes &&
        a.priceTicks == b.priceTicks && a.sequences == b.sequences &&
        a.traders == b.traders && a.lastSlots == b.lastSlots && a.lastTimes == b.lastTimes &&
        a.traderQuoteLocked == b.traderQuoteLocked &&
        a.traderQuoteFree == b.traderQuoteFree &&
        a.traderBaseLocked == b.traderBaseLocked &&
        a.traderBaseFree == b.traderBaseFree &&
        a.quoteLocked == b.quoteLocked && a.quoteFree == b.quoteFree &&
        a.baseLocked == b.baseLocked && a.baseFree == b.baseFree &&
        a.unclaimedFees == b.unclaimedFees && a.collectedFees == b.collectedFees &&
        a.events == b.events && a.eventCount == b.eventCount && a.lastEvent == b.lastEvent
  | _, _ => false

private def sameSellResult :
    Except Error (Projects.Phoenix.State × UInt64) →
      Except Error (Projects.Phoenix.State × UInt64) → Bool
  | .error a, .error b => a == b
  | .ok (a, ar), .ok (b, br) =>
      ar == br && a.bidSizes == b.bidSizes &&
        a.bidPriceTicks == b.bidPriceTicks && a.bidSequences == b.bidSequences &&
        a.bidTraders == b.bidTraders &&
        a.bidLastSlots == b.bidLastSlots && a.bidLastTimes == b.bidLastTimes &&
        a.traderQuoteLocked == b.traderQuoteLocked &&
        a.traderQuoteFree == b.traderQuoteFree &&
        a.traderBaseLocked == b.traderBaseLocked &&
        a.traderBaseFree == b.traderBaseFree &&
        a.quoteLocked == b.quoteLocked && a.quoteFree == b.quoteFree &&
        a.baseLocked == b.baseLocked && a.baseFree == b.baseFree &&
        a.unclaimedFees == b.unclaimedFees && a.collectedFees == b.collectedFees &&
        a.events == b.events && a.eventCount == b.eventCount && a.lastEvent == b.lastEvent
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
        (swapBuy s 0 0 0 want.toUInt64 limit.toUInt64)

#guard
  let expiredBook :=
    { (init 1) with
      sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
      sequences := #v[1, 2, 0, 0], lastSlots := #v[9, 0, 0, 0],
      quoteLocked := 1000, baseLocked := 5 }
  sameBusinessResult
    (swapBuyAt expiredBook 4 20 10 0)
    (swapBuyAt expiredBook 4 20 0 0) == false

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
        (swapSell s 0 0 0 want.toUInt64 limit.toUInt64)

#guard (init 100).tickSize == 100
#guard (init 100).sequence == 1
#guard (init 100).takerFeeBps == 5
#guard (init 100).sizes[0]! == 0
#guard (init 100).priceTicks[0]! == 0
#guard (init 100).bidPriceTicks[0]! == 0
#guard (init 100).traderCount == 0
#guard (init 100).traderBumpIndex == 1
#guard (init 100).traderFreeHead == 1
#guard (init 100).traderUsed == empty4
#guard (init 100).traderBaseFree == empty4
#guard (init 100).baseLocked == 0
#guard (init 100).baseFree == 0
#guard (init 100).eventCount == 0
#guard (init 100).events[0]! == MarketEvent.uninitialized
#guard (init 100).lastEvent == MarketEvent.uninitialized
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
  match depositFundsFor (init 1) 11 12 13 14 7 9 with
  | .ok (st, address) =>
      address == 1 && st.traderCount == 1 && st.traderBumpIndex == 2 &&
        st.traderFreeHead == 2 && st.traderUsed == #v[1, 0, 0, 0] &&
        st.traderKey0[0]! == 11 && st.traderKey1[0]! == 12 &&
        st.traderKey2[0]! == 13 && st.traderKey3[0]! == 14 &&
        st.traderBaseFree[0]! == 7 && st.traderQuoteFree[0]! == 9 &&
        st.baseFree == 7 && st.quoteFree == 9 &&
        traderIndexOf st 11 12 13 14 == 1 && traderBaseFreeAt st 1 == 7
  | .error _ => false

#guard
  match depositFundsFor (init 1) 0 0 0 0 0 0 with
  | .ok (st, address) =>
      address == 1 && st.traderUsed[0]! == 1 && traderIndexOf st 0 0 0 0 == 1
  | .error _ => false

#guard
  match depositFundsFor (init 1) 11 12 13 14 7 9 with
  | .error _ => false
  | .ok (s1, _) =>
    match depositFundsFor s1 11 12 13 14 5 6 with
    | .ok (s2, address) =>
        address == 1 && s2.traderCount == 1 && s2.traderBumpIndex == 2 &&
          s2.traderBaseFree[0]! == 12 && s2.traderQuoteFree[0]! == 15 &&
          s2.baseFree == 12 && s2.quoteFree == 15
    | .error _ => false

#guard
  match depositFundsFor (init 1) 1 10 20 30 1 2 with
  | .error _ => false
  | .ok (s1, a1) =>
    match depositFundsFor s1 1 10 20 31 3 4 with
    | .ok (s2, a2) =>
        a1 == 1 && a2 == 2 && s2.traderCount == 2 &&
          traderIndexOf s2 1 10 20 30 == 1 && traderIndexOf s2 1 10 20 31 == 2
    | .error _ => false

#guard
  match depositFundsFor (init 1) 1 0 0 0 1 0 with
  | .error _ => false
  | .ok (s1, _) =>
    match depositFundsFor s1 2 0 0 0 1 0 with
    | .error _ => false
    | .ok (s2, _) =>
      match depositFundsFor s2 3 0 0 0 1 0 with
      | .error _ => false
      | .ok (s3, _) =>
        match depositFundsFor s3 4 0 0 0 1 0 with
        | .error _ => false
        | .ok (s4, a4) =>
          a4 == 4 && s4.traderCount == 4 && s4.traderBumpIndex == 5 &&
            s4.traderFreeHead == 5 &&
            match depositFundsFor s4 5 0 0 0 1 0 with
            | .error .full => true
            | _ => false

#guard
  let s := { (init 1) with
    traderCount := 1, traderBumpIndex := 2, traderFreeHead := 2,
    traderUsed := #v[1, 0, 0, 0], traderKey0 := #v[9, 0, 0, 0],
    traderBaseFree := #v[u64Max, 0, 0, 0] }
  match depositFundsFor s 9 0 0 0 1 0 with
  | .error .overflow => true
  | _ => false

#guard
  match depositFundsFor (init 1) 11 12 13 14 7 9 with
  | .error _ => false
  | .ok (s1, _) =>
    match withdrawBaseFor s1 11 12 13 14 5 with
    | .error _ => false
    | .ok (s2, baseOut) =>
      match withdrawQuoteFor s2 11 12 13 14 20 with
      | .error _ => false
      | .ok (s3, quoteOut) =>
        match withdrawBaseFor s3 11 12 13 14 9 with
        | .error _ => false
        | .ok (s4, finalBaseOut) =>
          match evictSeatFor s4 11 12 13 14 with
          | .ok (s5, address) =>
              baseOut == 5 && quoteOut == 9 && finalBaseOut == 2 && address == 1 &&
                s5.baseFree == 0 && s5.quoteFree == 0 &&
                s5.traderCount == 0 && s5.traderBumpIndex == 2 &&
                s5.traderFreeHead == 1 && s5.traderNextFree[0]! == 2 &&
                s5.traderUsed[0]! == 0 && s5.traderKey0[0]! == 0
          | .error _ => false

#guard
  match withdrawBaseFor (init 1) 99 0 0 0 1 with
  | .error .unauthorized => true
  | _ => false

#guard
  match depositFundsFor (init 1) 1 0 0 0 0 0 with
  | .error _ => false
  | .ok (s1, _) =>
    let locked := { s1 with traderBaseLocked := s1.traderBaseLocked.set 0 1 }
    match evictSeatFor locked 1 0 0 0 with
    | .error .overflow => true
    | _ => false

#guard
  match depositFundsFor (init 1) 1 0 0 0 0 0 with
  | .error _ => false
  | .ok (s1, _) =>
    match depositFundsFor s1 2 0 0 0 0 0 with
    | .error _ => false
    | .ok (s2, _) =>
      match evictSeatFor s2 2 0 0 0 with
      | .error _ => false
      | .ok (s3, a2) =>
        match evictSeatFor s3 1 0 0 0 with
        | .error _ => false
        | .ok (s4, a1) =>
          match depositFundsFor s4 9 0 0 0 0 0 with
          | .error _ => false
          | .ok (s5, reused1) =>
            match depositFundsFor s5 8 0 0 0 0 0 with
            | .ok (s6, reused2) =>
                a2 == 2 && a1 == 1 && reused1 == 1 && reused2 == 2 &&
                  s6.traderCount == 2 && s6.traderBumpIndex == 3 &&
                  s6.traderFreeHead == 3 && traderIndexOf s6 9 0 0 0 == 1 &&
                  traderIndexOf s6 8 0 0 0 == 2
            | .error _ => false

#guard
  match postAskAt { (init 100) with baseFree := 8 } 7 50 8 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && st.priceTicks[0]! == 50 && st.traders[0]! == 7 &&
        st.sequences[0]! == 1 && st.sequence == 2 &&
        st.baseLocked == 8 && st.baseFree == 0 && ret == 8 &&
        st.eventCount == 1 && st.events[0]! == .place 0 1 0 0 50 8 &&
        st.lastEvent == .place 0 1 0 0 50 8
  | .error _ => false

#guard
  match postAskAt
      { (withSeats12 (init 100)) with
        traderBaseFree := #v[8, 0, 0, 0], baseFree := 8 }
      1 50 8 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes[0]! == 8 && st.traders[0]! == 1 &&
        st.traderBaseLocked == #v[8, 0, 0, 0] &&
        st.traderBaseFree == #v[0, 0, 0, 0] &&
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
  | .error .full => true
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
        st.baseLocked == 7 && st.baseFree == 4 && orderedAsks st && ret == 1 &&
        st.eventCount == 2 && st.events[0]! == .evict 0 4 0 0 0 4 40 4 &&
        st.events[1]! == .place 1 5 0 0 15 1
  | .error _ => false

#guard
  match postAskAt
      { (withSeats12 (init 100)) with
        sizes := #v[1, 2, 3, 4], priceTicks := #v[10, 20, 30, 40],
        sequences := #v[1, 2, 3, 4], traders := #v[2, 2, 2, 2],
        sequence := 5, traderBaseLocked := #v[0, 10, 0, 0],
        traderBaseFree := #v[1, 0, 0, 0], baseLocked := 10, baseFree := 1 }
      1 15 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[1, 1, 2, 3] && st.traders == #v[2, 1, 2, 2] &&
        st.traderBaseLocked == #v[1, 6, 0, 0] &&
        st.traderBaseFree == #v[0, 4, 0, 0] &&
        st.baseLocked == 7 && st.baseFree == 4 && ret == 1 &&
        st.events[0]! == .evict 0 22 23 24 25 4 40 4
  | .error _ => false

#guard
  match postAskAt
      { (init 100) with baseFree := 8 }
      7 50 8 9 0 10 0 with
  | .ok (st, ret) => st == { (init 100) with baseFree := 8 } && ret == 0
  | .error _ => false

#guard
  match postAskWithClientAt
      { (init 100) with baseFree := 8 }
      7 50 8 9 10 10 20 10 19 with
  | .ok (st, ret) =>
      ret == 8 && st.eventCount == 2 &&
        st.events[0]! == .place 0 1 9 10 50 8 &&
        st.events[1]! == .timeInForce 1 1 10 20 &&
        st.lastEvent == .timeInForce 1 1 10 20
  | .error _ => false

#guard
  match postBidAt { (init 1) with quoteFree := 100 } 7 50 2 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[2, 0, 0, 0] && st.bidPriceTicks == #v[50, 0, 0, 0] &&
        st.bidTraders[0]! == 7 && st.bidSequences[0]! == ~~~(1 : UInt64) &&
        st.sequence == 2 && st.quoteLocked == 100 && st.quoteFree == 0 && ret == 2 &&
        st.lastEvent == .place 0 1 0 0 50 2
  | .error _ => false

#guard
  match postBidAt
      { (withSeats12 (init 1)) with
        traderQuoteFree := #v[100, 0, 0, 0], quoteFree := 100 }
      1 50 2 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes[0]! == 2 && st.bidTraders[0]! == 1 &&
        st.traderQuoteLocked == #v[100, 0, 0, 0] &&
        st.traderQuoteFree == #v[0, 0, 0, 0] &&
        st.quoteLocked == 100 && st.quoteFree == 0 && ret == 2
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
      { (withSeats12 (init 1)) with
        bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[40, 30, 20, 10],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64),
          ~~~(3 : UInt64), ~~~(4 : UInt64)],
        bidTraders := #v[2, 2, 2, 2], sequence := 5,
        traderQuoteLocked := #v[0, 100, 0, 0],
        traderQuoteFree := #v[100, 0, 0, 0], quoteLocked := 100, quoteFree := 100 }
      1 25 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 1, 1, 1] && st.bidTraders == #v[2, 2, 1, 2] &&
        st.traderQuoteLocked == #v[25, 90, 0, 0] &&
        st.traderQuoteFree == #v[75, 10, 0, 0] &&
        st.quoteLocked == 115 && st.quoteFree == 85 && ret == 1 &&
        st.events[0]! == .evict 0 22 23 24 25 4 10 1
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with
        bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[40, 30, 20, 10],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64),
          ~~~(3 : UInt64), ~~~(4 : UInt64)],
        bidTraders := #v[1, 2, 3, 4],
        sequence := 5, quoteLocked := 100, quoteFree := 100 }
      9 25 1 0 0 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 1, 1, 1] && st.bidPriceTicks == #v[40, 30, 25, 20] &&
        st.quoteLocked == 115 && st.quoteFree == 85 && orderedBids st && ret == 1 &&
        st.eventCount == 2 && st.events[0]! == .evict 0 4 0 0 0 4 10 1 &&
        st.events[1]! == .place 1 5 0 0 25 1
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with
        bidSizes := #v[1, 1, 1, 1], bidPriceTicks := #v[40, 30, 20, 10],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64),
          ~~~(3 : UInt64), ~~~(4 : UInt64)],
        sequence := 5, quoteLocked := 100, quoteFree := 100 }
      9 10 1 0 0 0 0 with
  | .error .full => true
  | _ => false

#guard
  match postBidAt { (init 1) with quoteFree := 100 } 7 50 2 9 0 10 0 with
  | .ok (st, ret) => st == { (init 1) with quoteFree := 100 } && ret == 0
  | .error _ => false

#guard
  match postBidAt
      { (init 1) with quoteFree := 100 }
      7 50 2 10 20 10 19 with
  | .ok (st, ret) =>
      ret == 2 && st.eventCount == 2 &&
        st.events[0]! == .place 0 1 0 0 50 2 &&
        st.events[1]! == .timeInForce 1 1 10 20 &&
        st.lastEvent == .timeInForce 1 1 10 20
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 3, 5, 0], priceTicks := #v[10, 11, 12, 0],
        sequences := #v[1, 2, 3, 0], traders := #v[7, 8, 9, 0],
        quoteLocked := 1000, baseLocked := 10 }
      4 11 0 0 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 1000 && st.quoteFree == 42 &&
        st.baseLocked == 6 && st.baseFree == 0 &&
        st.unclaimedFees == 1 && st.collectedFees == 0 &&
        st.eventCount == 3 &&
        st.events[0]! == .fill 0 7 0 0 0 1 10 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 4 42 1 &&
        st.lastEvent == .fillSummary 2 0 0 4 42 1
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        lastSlots := #v[9, 0, 0, 0], quoteLocked := 100, baseLocked := 5 }
      2 11 10 0 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 100 && st.quoteFree == 22 &&
        st.baseLocked == 1 && st.baseFree == 2 && st.unclaimedFees == 1 &&
        st.eventCount == 3 &&
        st.events[0]! == .expiredOrder 0 0 0 0 0 0 10 2 &&
        st.events[1]! == .fill 1 0 0 0 0 0 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 2 22 1
  | .error _ => false

#guard
  match swapBuyAt
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        lastSlots := #v[10, 0, 0, 0], lastTimes := #v[10, 0, 0, 0],
        quoteLocked := 100, baseLocked := 2 }
      1 10 10 10 with
  | .ok (st, ret) => st.sizes[0]! == 1 && ret == 1 && st.baseFree == 0
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
        sizes := #v[1, 0, 0, 0], lastSlots := #v[1, 0, 0, 0], baseLocked := 1,
        quoteLocked := 2, baseFree := u64Max }
      1 0 2 0 with
  | .error .overflow => true
  | _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 3, 5, 0], priceTicks := #v[10, 11, 12, 0],
        sequences := #v[1, 2, 3, 0], traders := #v[7, 8, 9, 0],
        quoteLocked := 1000, baseLocked := 10 }
      0 11 12 4 11 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 1000 && st.quoteFree == 42 &&
        st.baseLocked == 6 && st.baseFree == 0 && st.unclaimedFees == 1 &&
        st.eventCount == 3 &&
        st.events[0]! == .fill 0 7 0 0 0 1 10 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 11 12 4 42 1 &&
        st.lastEvent == .fillSummary 2 11 12 4 42 1
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[11, 0, 0, 0],
        quoteLocked := 100, baseLocked := 2 }
      0 0 0 1 10 with
  | .ok (st, ret) => st.sizes[0]! == 2 && ret == 0
  | .error _ => false

#guard
  match swapBuy
      { (init 1) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        baseLocked := 2 }
      0 0 0 0 10 with
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
  | .error .selfTrade => true
  | _ => false

#guard
  match swapBuyForAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[7, 8, 0, 0],
        quoteLocked := 1000, baseLocked := 5 }
      7 2 11 0 0 .cancelProvide with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 1000 && st.quoteFree == 22 &&
        st.baseLocked == 1 && st.baseFree == 2 && st.unclaimedFees == 1 &&
        st.eventCount == 3 && st.events[0]! == .reduce 0 1 10 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 2 22 1
  | .error _ => false

#guard
  match swapBuyForAt
      { (init 1) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[7, 8, 0, 0],
        quoteLocked := 1000, baseLocked := 5 }
      7 1 11 0 0 .decrementTake with
  | .ok (st, ret) =>
      st.sizes == #v[1, 3, 0, 0] && ret == 0 &&
        st.quoteLocked == 1000 && st.quoteFree == 0 &&
        st.baseLocked == 4 && st.baseFree == 1 && st.unclaimedFees == 0 &&
        st.eventCount == 2 && st.events[0]! == .reduce 0 1 10 1 1 &&
        st.events[1]! == .fillSummary 1 0 0 0 0 0
  | .error _ => false

#guard
  match swapBuy
      { (withSeats12 (init 1)) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[1, 2, 0, 0],
        traderQuoteFree := #v[1000, 0, 0, 0],
        traderBaseLocked := #v[2, 3, 0, 0], quoteFree := 1000, baseLocked := 5 }
      1 0 0 2 11 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.traderQuoteLocked == #v[0, 0, 0, 0] &&
        st.traderQuoteFree == #v[977, 22, 0, 0] && st.quoteFree == 999 &&
        st.traderBaseLocked == #v[0, 1, 0, 0] &&
        st.traderBaseFree == #v[4, 0, 0, 0] &&
        st.baseLocked == 1 && st.baseFree == 4 && st.unclaimedFees == 1 &&
        st.eventCount == 3 && st.events[0]! == .reduce 0 1 10 2 0 &&
        st.events[1]! == .fill 1 22 23 24 25 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 2 22 1
  | .error _ => false

#guard
  match swapBuyForAt
      { (withSeats12 (init 1)) with
        sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
        traders := #v[2, 2, 0, 0], lastSlots := #v[9, 0, 0, 0],
        traderQuoteFree := #v[1000, 0, 0, 0],
        traderBaseLocked := #v[0, 5, 0, 0], quoteFree := 1000, baseLocked := 5 }
      1 2 11 10 0 .abort with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.traderQuoteLocked == #v[0, 0, 0, 0] &&
        st.traderQuoteFree == #v[977, 22, 0, 0] && st.quoteFree == 999 &&
        st.traderBaseLocked == #v[0, 1, 0, 0] &&
        st.traderBaseFree == #v[2, 2, 0, 0] &&
        st.events[0]! == .expiredOrder 0 22 23 24 25 0 10 2 &&
        st.events[1]! == .fill 1 22 23 24 25 0 11 2 1
  | .error _ => false

#guard
  match swapBuyForAt
      { (withSeats12 (init 1)) with
        sizes := #v[1, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        traders := #v[2, 0, 0, 0], traderQuoteFree := #v[100, 0, 0, 0],
        quoteFree := 100, baseLocked := 1 }
      1 1 10 0 0 .abort with
  | .error .overflow => true
  | _ => false

#guard
  let s :=
    { (withSeats12 (init 1)) with
      sizes := #v[2, 3, 0, 0], priceTicks := #v[10, 11, 0, 0],
      sequences := #v[1, 2, 0, 0], traders := #v[1, 2, 0, 0],
      traderQuoteFree := #v[1000, 0, 0, 0],
      traderBaseLocked := #v[2, 3, 0, 0], quoteFree := 1000, baseLocked := 5 }
  sameBusinessResult
    (swapBuyForAt s 1 1 11 0 0 .decrementTake)
    (swapBuy s 2 0 0 1 11)

#guard
  match swapSellAt
      { (init 1) with
        bidSizes := #v[2, 3, 5, 0], bidPriceTicks := #v[12, 11, 10, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), ~~~(3 : UInt64), 0],
        bidTraders := #v[7, 8, 9, 0],
        quoteLocked := 107 }
      4 11 0 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 61 && st.quoteFree == 0 && st.baseFree == 4 &&
        st.unclaimedFees == 1 && st.eventCount == 3 &&
        st.events[0]! == .fill 0 7 0 0 0 1 12 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 4 46 1
  | .error _ => false

#guard
  match swapSell
      { (init 1) with
        bidSizes := #v[2, 3, 5, 0], bidPriceTicks := #v[12, 11, 10, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), ~~~(3 : UInt64), 0],
        bidTraders := #v[7, 8, 9, 0],
        quoteLocked := 107 }
      0 13 14 4 11 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 5, 0] && ret == 4 &&
        st.quoteLocked == 61 && st.quoteFree == 0 && st.baseFree == 4 &&
        st.unclaimedFees == 1 && st.eventCount == 3 &&
        st.events[0]! == .fill 0 7 0 0 0 1 12 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 13 14 4 46 1
  | .error _ => false

#guard
  match swapSellAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[7, 8, 0, 0], bidLastSlots := #v[9, 0, 0, 0],
        quoteLocked := 57 }
      2 11 10 0 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 11 && st.quoteFree == 24 && st.baseFree == 2 &&
        st.unclaimedFees == 1 &&
        st.eventCount == 3 && st.events[0]! == .expiredOrder 0 7 0 0 0 1 12 2 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 2 22 1
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
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57 }
      7 2 11 0 0 .abort with
  | .error .selfTrade => true
  | _ => false

#guard
  match swapSellForAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57 }
      7 2 11 0 0 .cancelProvide with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.quoteLocked == 11 && st.quoteFree == 24 && st.baseFree == 2 &&
        st.unclaimedFees == 1 &&
        st.eventCount == 3 && st.events[0]! == .reduce 0 1 12 2 0 &&
        st.events[1]! == .fill 1 8 0 0 0 2 11 2 1 &&
        st.events[2]! == .fillSummary 2 0 0 2 22 1
  | .error _ => false

#guard
  match swapSellForAt
      { (init 1) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[7, 8, 0, 0], quoteLocked := 57, baseFree := 1 }
      7 1 11 0 0 .decrementTake with
  | .ok (st, ret) =>
      st.bidSizes == #v[1, 3, 0, 0] && ret == 0 &&
        st.quoteLocked == 45 && st.quoteFree == 12 && st.baseFree == 1 &&
        st.unclaimedFees == 0 && st.eventCount == 2 &&
        st.events[0]! == .reduce 0 1 12 1 1 &&
        st.events[1]! == .fillSummary 1 0 0 0 0 0
  | .error _ => false

#guard
  match swapSell
    { (withSeats12 (init 1)) with
      bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
      bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
      bidTraders := #v[1, 2, 0, 0], traderQuoteLocked := #v[24, 33, 0, 0],
      traderBaseFree := #v[2, 0, 0, 0], quoteLocked := 57, baseFree := 2 }
    1 0 0 2 11 with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.traderQuoteLocked == #v[0, 11, 0, 0] &&
        st.traderQuoteFree == #v[45, 0, 0, 0] &&
        st.traderBaseFree == #v[0, 2, 0, 0] &&
        st.quoteLocked == 11 && st.quoteFree == 45 && st.baseFree == 2 &&
        st.events[0]! == .reduce 0 1 12 2 0 &&
        st.events[1]! == .fill 1 22 23 24 25 2 11 2 1
  | .error _ => false

#guard
  match swapSellForAt
      { (withSeats12 (init 1)) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[2, 2, 0, 0], bidLastSlots := #v[9, 0, 0, 0],
        traderQuoteLocked := #v[0, 57, 0, 0],
        traderBaseFree := #v[2, 0, 0, 0], quoteLocked := 57, baseFree := 2 }
      1 2 11 10 0 .abort with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 1, 0, 0] && ret == 2 &&
        st.traderQuoteLocked == #v[0, 11, 0, 0] &&
        st.traderQuoteFree == #v[21, 24, 0, 0] &&
        st.traderBaseFree == #v[0, 2, 0, 0] &&
        st.events[0]! == .expiredOrder 0 22 23 24 25 1 12 2 &&
        st.events[1]! == .fill 1 22 23 24 25 2 11 2 1
  | .error _ => false

#guard
  let s :=
    { (withSeats12 (init 1)) with
      bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
      bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
      bidTraders := #v[1, 2, 0, 0], traderQuoteLocked := #v[24, 33, 0, 0],
      traderBaseFree := #v[2, 0, 0, 0], quoteLocked := 57, baseFree := 2 }
  sameSellResult
    (swapSellForAt s 1 2 11 0 0 .cancelProvide)
    (swapSell s 1 0 0 2 11)

#guard
  match sweepAsk { (init 100) with
      sizes := #v[2, 8, 0, 0], baseLocked := 10, baseFree := 0 } with
  | .ok (st, ret) =>
      st.sizes[0]! == 0 && st.sizes[1]! == 8 && st.baseLocked == 8 &&
        st.baseFree == 2 && ret == 2
  | .error _ => false

#guard
  match reduceAskAt
      { (withSeats12 (init 100)) with
        sizes := #v[8, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[1, 2, 0, 0],
        traderBaseLocked := #v[8, 1, 0, 0], traderBaseFree := #v[1, 0, 0, 0],
        baseLocked := 9, baseFree := 1 }
      1 10 1 3 with
  | .ok (st, ret) =>
      st.sizes == #v[5, 1, 0, 0] && st.baseLocked == 6 && st.baseFree == 4 &&
        st.traderBaseLocked == #v[5, 1, 0, 0] &&
        st.traderBaseFree == #v[4, 0, 0, 0] &&
        st.matchFilled == 0 && ret == 3 && st.eventCount == 1 &&
        st.events[0]! == .reduce 0 1 10 3 5 && st.lastEvent == .reduce 0 1 10 3 5
  | .error _ => false

#guard
  match reduceAskAt
      { (withSeats12 (init 100)) with
        sizes := #v[2, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
        sequences := #v[1, 2, 0, 0], traders := #v[1, 2, 0, 0],
        traderBaseLocked := #v[2, 1, 0, 0],
        baseLocked := 3 }
      1 10 1 9 with
  | .ok (st, ret) =>
      st.sizes == #v[0, 1, 0, 0] && st.baseLocked == 1 && st.baseFree == 2 &&
        st.traderBaseLocked == #v[0, 1, 0, 0] &&
        st.traderBaseFree == #v[2, 0, 0, 0] && ret == 2
  | .error _ => false

#guard
  match reduceAskAt
      { (withSeats12 (init 100)) with
        sizes := #v[2, 0, 0, 0], priceTicks := #v[10, 0, 0, 0],
        sequences := #v[1, 0, 0, 0], traders := #v[1, 0, 0, 0],
        traderBaseLocked := #v[2, 0, 0, 0], baseLocked := 2 }
      2 10 1 1 with
  | .error .overflow => true
  | _ => false

#guard
  match reduceBidAt
      { (withSeats12 (init 1)) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[1, 2, 0, 0], traderQuoteLocked := #v[24, 33, 0, 0],
        quoteLocked := 57 }
      2 11 (~~~(2 : UInt64)) 2 with
  | .ok (st, ret) =>
      st.bidSizes == #v[2, 1, 0, 0] && st.quoteLocked == 35 &&
        st.quoteFree == 22 && st.traderQuoteLocked == #v[24, 11, 0, 0] &&
        st.traderQuoteFree == #v[0, 22, 0, 0] && ret == 2 &&
        st.lastEvent == .reduce 0 (~~~(2 : UInt64)) 11 2 1
  | .error _ => false

#guard
  match cancelBid
      { (withSeats12 (init 1)) with
        bidSizes := #v[2, 3, 0, 0], bidPriceTicks := #v[12, 11, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), ~~~(2 : UInt64), 0, 0],
        bidTraders := #v[1, 2, 0, 0], traderQuoteLocked := #v[24, 33, 0, 0],
        quoteLocked := 57 }
      1 12 (~~~(1 : UInt64)) with
  | .ok (st, ret) =>
      st.bidSizes == #v[0, 3, 0, 0] && st.quoteLocked == 33 &&
        st.quoteFree == 24 && st.traderQuoteLocked == #v[0, 33, 0, 0] &&
        st.traderQuoteFree == #v[24, 0, 0, 0] && ret == 2
  | .error _ => false

#guard
  match reduceBidAt
      { (withSeats12 (init 1)) with
        bidSizes := #v[2, 0, 0, 0], bidPriceTicks := #v[12, 0, 0, 0],
        bidSequences := #v[~~~(1 : UInt64), 0, 0, 0],
        bidTraders := #v[1, 0, 0, 0], traderQuoteLocked := #v[24, 0, 0, 0],
        quoteLocked := 24 }
      2 12 (~~~(1 : UInt64)) 1 with
  | .error .overflow => true
  | _ => false

#guard
  match cancelAsk { (withSeats12 (init 100)) with
      sizes := #v[8, 1, 0, 0], priceTicks := #v[10, 20, 0, 0],
      sequences := #v[1, 2, 0, 0], traders := #v[1, 2, 0, 0],
      traderBaseLocked := #v[8, 1, 0, 0], baseLocked := 9 } 1 10 1 with
  | .ok (st, ret) => st.sizes[0]! == 0 && st.sizes[1]! == 1 &&
      st.baseLocked == 1 && st.baseFree == 8 &&
      st.traderBaseLocked == #v[0, 1, 0, 0] &&
      st.traderBaseFree == #v[8, 0, 0, 0] && ret == 8
  | .error _ => false

#guard
  match cancelAsk (withSeats12 (init 100)) 1 10 1 with
  | .ok (st, ret) => st == withSeats12 (init 100) && ret == 0
  | .error _ => false

#guard
  match collectFees { (init 100) with collectedFees := 9, unclaimedFees := 3 } with
  | .ok (st, ret) =>
      st.collectedFees == 12 && st.unclaimedFees == 0 && ret == 3 &&
        st.eventCount == 1 && st.events[0]! == .fee 0 3 &&
        st.lastEvent == .fee 0 3 && lastEventKind st == 7 && lastEventAmount st == 3
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
#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedPhoenix != 1376

#guard
  let full :=
    (appendEvent
      (appendEvent
        (appendEvent
          (appendEvent
            (appendEvent (init 1) (.fee 0 1))
            (.fee 1 1))
          (.fee 2 1))
        (.fee 3 1))
      (.fee 4 1))
  full.eventCount == 5 &&
    (appendEvent full (.fee 5 1)).matchError == matchFull &&
    (appendEvent full (.fee 5 1)).eventCount == 5

end Tests.PhoenixSpec
