import ProofForge.Attr
import ProofForge.Svm.AccountStorage.Source
import ProofForge.Svm.FifoCancel.Source

namespace Examples.PhoenixV1

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source

/-- Named scalar cells in Phoenix's fixed market header. Word offsets live here, not in contract
control flow. -/
structure Header where
  status : Field
  marketSequence : Field
  baseLotSize : Field
  quoteLotSize : Field
  baseLotsPerBaseUnit : Field
  tickSize : Field
  orderSequence : Field
  deriving BEq, Repr, Inhabited

/-- One side of the account-resident FIFO book plus its resting-order payload fields. -/
structure Book where
  map : RbMap
  nodeCount : Field
  owner : Field
  size : Field
  lastValidSlot : Field
  lastValidTime : Field
  deriving BEq, Repr, Inhabited

/-- The registered-trader map and its four balance fields. -/
structure Traders where
  map : RbMap
  quoteLocked : Field
  quoteFree : Field
  baseLocked : Field
  baseFree : Field
  deriving BEq, Repr, Inhabited

/-- A fully static Phoenix-compatible account profile. This is a compile-time layout instance, not
a runtime object and not an allocator. Future contracts can define other profiles using the same
`AccountStorage` handles. -/
structure Layout where
  account : Nat
  accountBytes : Nat
  header : Header
  bids : Book
  asks : Book
  traders : Traders
  deriving BEq, Repr, Inhabited

/- These projections only expose compile-time storage descriptors. Marking them explicitly keeps
the extractor generic: it erases opted-in static layout records without knowing this example's
namespace or protocol. -/
attribute [pf_inline]
  Header.status Header.marketSequence Header.baseLotSize Header.quoteLotSize
  Header.baseLotsPerBaseUnit Header.tickSize Header.orderSequence Book.map Book.nodeCount
  Book.owner Book.size Book.lastValidSlot Book.lastValidTime Traders.map Traders.quoteLocked
  Traders.quoteFree Traders.baseLocked Traders.baseFree Layout.account Layout.accountBytes
  Layout.header Layout.bids Layout.asks Layout.traders

@[pf_inline] private def mutableAccess : Access :=
  { writable := true, currentProgramOwned := true }

@[pf_inline] private def scalar (account word : Nat) : Field :=
  { region :=
      { account, baseWord := word, strideWords := 1, capacity := 1
        access := mutableAccess } }

@[pf_inline] private def oneBased (account word stride capacity : Nat) : Field :=
  { region :=
      { account, baseWord := word, strideWords := stride, capacity
        indexBase := .one, access := mutableAccess } }

/-- Official smallest compiled Phoenix-v1 market profile `(bids=512, asks=512, seats=128)`.
All raw offsets are centralized in this one instance. The profile is erased while extracting
source operations, so no descriptor or geometry is constructed at runtime. -/
@[pf_inline] def small (account : Nat) : Layout :=
  { account
    accountBytes := 84944
    header :=
      { status := scalar account 1
        marketSequence := scalar account 34
        baseLotSize := scalar account 14
        quoteLotSize := scalar account 24
        baseLotsPerBaseUnit := scalar account 104
        tickSize := scalar account 105
        orderSequence := scalar account 106 }
    bids :=
      { map := .fifoOneBased account 110 114 115 116 117 8 512 true
        nodeCount := scalar account 112
        owner := oneBased account 118 8 512
        size := oneBased account 119 8 512
        lastValidSlot := oneBased account 120 8 512
        lastValidTime := oneBased account 121 8 512 }
    asks :=
      { map := .fifoOneBased account 4210 4214 4215 4216 4217 8 512 false
        nodeCount := scalar account 4212
        owner := oneBased account 4218 8 512
        size := oneBased account 4219 8 512
        lastValidSlot := oneBased account 4220 8 512
        lastValidTime := oneBased account 4221 8 512 }
    traders :=
      { map := .key4OneBased account 8310 8314 8315 8316 18 128
        quoteLocked := oneBased account 8320 18 128
        quoteFree := oneBased account 8321 18 128
        baseLocked := oneBased account 8322 18 128
        baseFree := oneBased account 8323 18 128 } }

def Layout.wellFormed (layout : Layout) : Bool :=
  layout.account > 0 && layout.accountBytes > 0 &&
    layout.bids.map.wellFormed && layout.asks.map.wellFormed &&
    layout.traders.map.wellFormed &&
    layout.header.status.wellFormed && layout.header.marketSequence.wellFormed &&
    layout.header.baseLotSize.wellFormed && layout.header.quoteLotSize.wellFormed &&
    layout.header.baseLotsPerBaseUnit.wellFormed && layout.header.tickSize.wellFormed &&
    layout.header.orderSequence.wellFormed &&
    layout.bids.nodeCount.wellFormed && layout.bids.owner.wellFormed &&
    layout.bids.size.wellFormed && layout.bids.lastValidSlot.wellFormed &&
    layout.bids.lastValidTime.wellFormed && layout.asks.nodeCount.wellFormed &&
    layout.asks.owner.wellFormed && layout.asks.size.wellFormed &&
    layout.asks.lastValidSlot.wellFormed && layout.asks.lastValidTime.wellFormed &&
    layout.traders.quoteLocked.wellFormed && layout.traders.quoteFree.wellFormed &&
    layout.traders.baseLocked.wellFormed && layout.traders.baseFree.wellFormed

@[pf_inline] def Layout.status (layout : Layout) : UInt64 := read layout.header.status 0
@[pf_inline] def Layout.marketSequence (layout : Layout) : UInt64 :=
  read layout.header.marketSequence 0
@[pf_inline] def Layout.orderSequence (layout : Layout) : UInt64 :=
  read layout.header.orderSequence 0
@[pf_inline] def Layout.baseLotSize (layout : Layout) : UInt64 :=
  read layout.header.baseLotSize 0
@[pf_inline] def Layout.quoteLotSize (layout : Layout) : UInt64 :=
  read layout.header.quoteLotSize 0
@[pf_inline] def Layout.baseLotsPerBaseUnit (layout : Layout) : UInt64 :=
  read layout.header.baseLotsPerBaseUnit 0
@[pf_inline] def Layout.tickSize (layout : Layout) : UInt64 :=
  read layout.header.tickSize 0

@[pf_inline] def Layout.bidSize (layout : Layout) : UInt64 := read layout.bids.nodeCount 0
@[pf_inline] def Layout.askSize (layout : Layout) : UInt64 := read layout.asks.nodeCount 0

@[pf_inline] def Layout.tradersValid (layout : Layout) : UInt64 :=
  validate layout.traders.map
@[pf_inline] def Layout.bidsValid (layout : Layout) : UInt64 :=
  validate layout.bids.map
@[pf_inline] def Layout.asksValid (layout : Layout) : UInt64 :=
  validate layout.asks.map

/-- Build one reusable bounded cancellation plan from the named bid book, trader balance fields,
and an independently supplied audit sink. All geometry remains compile-time data. -/
@[pf_inline] def Layout.bidCancelConfig (layout : Layout)
    (recorder : ProofForge.Svm.BatchRecorder.Config) : ProofForge.Svm.FifoCancel.Config :=
  { map := layout.bids.map
    owner := layout.bids.owner
    size := layout.bids.size
    locked := layout.traders.quoteLocked
    free := layout.traders.quoteFree
    collateral := .quote layout.header.baseLotsPerBaseUnit.firstWord
      layout.header.tickSize.firstWord
    recorder }

/-- Build the corresponding ask-side plan. Base collateral needs no price-header geometry. -/
@[pf_inline] def Layout.askCancelConfig (layout : Layout)
    (recorder : ProofForge.Svm.BatchRecorder.Config) : ProofForge.Svm.FifoCancel.Config :=
  { map := layout.asks.map
    owner := layout.asks.owner
    size := layout.asks.size
    locked := layout.traders.baseLocked
    free := layout.traders.baseFree
    collateral := .base
    recorder }

@[pf_inline] def Layout.findTrader (layout : Layout) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  findKey4 layout.traders.map key0 key1 key2 key3

@[pf_inline] def Layout.findBid (layout : Layout) (price sequence : UInt64) : UInt64 :=
  findFifo layout.bids.map price sequence

@[pf_inline] def Layout.findAsk (layout : Layout) (price sequence : UInt64) : UInt64 :=
  findFifo layout.asks.map price sequence

@[pf_inline] def Layout.insertBid (layout : Layout)
    (price sequence owner size lastSlot lastTime : UInt64) : UInt64 :=
  insertFifo layout.bids.map price sequence owner size lastSlot lastTime

@[pf_inline] def Layout.insertAsk (layout : Layout)
    (price sequence owner size lastSlot lastTime : UInt64) : UInt64 :=
  insertFifo layout.asks.map price sequence owner size lastSlot lastTime

@[pf_inline] def Layout.removeBid (layout : Layout) (price sequence : UInt64) : UInt64 :=
  removeFifo layout.bids.map price sequence
@[pf_inline] def Layout.removeAsk (layout : Layout) (price sequence : UInt64) : UInt64 :=
  removeFifo layout.asks.map price sequence

@[pf_inline] def Layout.bidOwner (layout : Layout) (order : UInt64) : UInt64 :=
  read layout.bids.owner order
@[pf_inline] def Layout.bidOrderSize (layout : Layout) (order : UInt64) : UInt64 :=
  read layout.bids.size order
@[pf_inline] def Layout.askOwner (layout : Layout) (order : UInt64) : UInt64 :=
  read layout.asks.owner order
@[pf_inline] def Layout.askOrderSize (layout : Layout) (order : UInt64) : UInt64 :=
  read layout.asks.size order

@[pf_inline] def Layout.setBidOrderSize (layout : Layout) (order value : UInt64) : UInt64 :=
  write layout.bids.size order value
@[pf_inline] def Layout.setAskOrderSize (layout : Layout) (order value : UInt64) : UInt64 :=
  write layout.asks.size order value

@[pf_inline] def Layout.quoteLocked (layout : Layout) (trader : UInt64) : UInt64 :=
  read layout.traders.quoteLocked trader
@[pf_inline] def Layout.quoteFree (layout : Layout) (trader : UInt64) : UInt64 :=
  read layout.traders.quoteFree trader
@[pf_inline] def Layout.baseLocked (layout : Layout) (trader : UInt64) : UInt64 :=
  read layout.traders.baseLocked trader
@[pf_inline] def Layout.baseFree (layout : Layout) (trader : UInt64) : UInt64 :=
  read layout.traders.baseFree trader

@[pf_inline] def Layout.setQuoteLocked (layout : Layout) (trader value : UInt64) : UInt64 :=
  write layout.traders.quoteLocked trader value
@[pf_inline] def Layout.setQuoteFree (layout : Layout) (trader value : UInt64) : UInt64 :=
  write layout.traders.quoteFree trader value
@[pf_inline] def Layout.setBaseLocked (layout : Layout) (trader value : UInt64) : UInt64 :=
  write layout.traders.baseLocked trader value
@[pf_inline] def Layout.setBaseFree (layout : Layout) (trader value : UInt64) : UInt64 :=
  write layout.traders.baseFree trader value


@[pf_inline] def Layout.setOrderSequence (layout : Layout) (value : UInt64) : UInt64 :=
  write layout.header.orderSequence 0 value

@[pf_inline] def Layout.setMarketSequence (layout : Layout) (value : UInt64) : UInt64 :=
  write layout.header.marketSequence 0 value

end Examples.PhoenixV1
