import ProofForge.Attr
import ProofForge.Svm.AccountStorage.Source
import ProofForge.Svm.FifoCancel.Source

namespace Examples.Svm.PhoenixV1

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
  takerFeeBps : Field
  collectedQuoteFees : Field
  unclaimedQuoteFees : Field
  deriving BEq, Repr, Inhabited

/-- Phoenix builds its price-time FIFO book above the generic SDK from one ordered map and four
fixed-record payload fields. The SDK itself does not know owners, lot sizes, or time-in-force. -/
structure Book where
  map : RbMap
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
  Header.baseLotsPerBaseUnit Header.tickSize Header.orderSequence Header.takerFeeBps
  Header.collectedQuoteFees Header.unclaimedQuoteFees Book.map Book.owner Book.size Book.lastValidSlot
  Book.lastValidTime Traders.map Traders.quoteLocked Traders.quoteFree Traders.baseLocked
  Traders.baseFree Layout.account Layout.accountBytes Layout.header Layout.bids Layout.asks
  Layout.traders

/-- Official smallest compiled Phoenix-v1 market profile `(bids=512, asks=512, seats=128)`.
All raw offsets are centralized in this one instance. The profile is erased while extracting
source operations, so no descriptor or geometry is constructed at runtime. -/
@[pf_inline] def small (account : Nat) : Layout :=
  { account
    accountBytes := 84944
    header :=
      { status := Field.scalar account 1
        marketSequence := Field.scalar account 34
        baseLotSize := Field.scalar account 14
        quoteLotSize := Field.scalar account 24
        baseLotsPerBaseUnit := Field.scalar account 104
        tickSize := Field.scalar account 105
        orderSequence := Field.scalar account 106
        takerFeeBps := Field.scalar account 107
        collectedQuoteFees := Field.scalar account 108
        unclaimedQuoteFees := Field.scalar account 109 }
    bids :=
      { map := .orderedPairOneBased account 110 114 115 116 117 8 512 true
        owner := Field.oneBased account 118 8 512
        size := Field.oneBased account 119 8 512
        lastValidSlot := Field.oneBased account 120 8 512
        lastValidTime := Field.oneBased account 121 8 512 }
    asks :=
      { map := .orderedPairOneBased account 4210 4214 4215 4216 4217 8 512 false
        owner := Field.oneBased account 4218 8 512
        size := Field.oneBased account 4219 8 512
        lastValidSlot := Field.oneBased account 4220 8 512
        lastValidTime := Field.oneBased account 4221 8 512 }
    traders :=
      { map := .key4OneBased account 8310 8314 8315 8316 18 128
        quoteLocked := Field.oneBased account 8320 18 128
        quoteFree := Field.oneBased account 8321 18 128
        baseLocked := Field.oneBased account 8322 18 128
        baseFree := Field.oneBased account 8323 18 128 } }

/-- Validate the Phoenix-level record schema using only generic SDK predicates. -/
def Book.wellFormed (book : Book) (accountLimit : Nat := 64) : Bool :=
  book.map.wellFormed accountLimit && book.map.allocator.wellFormed accountLimit &&
    match book.map with
    | .key4 .. => false
    | .fifo _ tree =>
        book.owner.mutableOneBasedWord accountLimit &&
          book.size.mutableOneBasedWord accountLimit &&
          book.lastValidSlot.mutableOneBasedWord accountLimit &&
          book.lastValidTime.mutableOneBasedWord accountLimit &&
          book.owner.region.sameShape tree.links.region &&
          book.size.region.sameShape tree.links.region &&
          book.lastValidSlot.region.sameShape tree.links.region &&
          book.lastValidTime.region.sameShape tree.links.region

@[pf_inline] def Book.count (book : Book) : UInt64 := liveCount book.map
@[pf_inline] def Book.validate (book : Book) : UInt64 :=
  ProofForge.Svm.AccountStorage.Source.validate book.map
@[pf_inline] def Book.find (book : Book) (price sequence : UInt64) : UInt64 :=
  findOrderedPair book.map price sequence
@[pf_inline] def Book.cursor (book : Book) (hasCursor price sequence : UInt64) : UInt64 :=
  cursorOrderedPair book.map hasCursor price sequence
@[pf_inline] def Book.price (book : Book) (order : UInt64) : UInt64 :=
  orderedKey0 book.map order
@[pf_inline] def Book.sequence (book : Book) (order : UInt64) : UInt64 :=
  orderedKey1 book.map order
@[pf_inline] def Book.ownerAt (book : Book) (order : UInt64) : UInt64 := read book.owner order
@[pf_inline] def Book.sizeAt (book : Book) (order : UInt64) : UInt64 := read book.size order
@[pf_inline] def Book.lastSlotAt (book : Book) (order : UInt64) : UInt64 :=
  read book.lastValidSlot order
@[pf_inline] def Book.lastTimeAt (book : Book) (order : UInt64) : UInt64 :=
  read book.lastValidTime order
@[pf_inline] def Book.setSizeAt (book : Book) (order value : UInt64) : UInt64 :=
  write book.size order value
@[pf_inline] def Book.setSizeOrRemove (book : Book)
    (order price sequence value : UInt64) : UInt64 :=
  setWordOrRemoveOrderedPair book.map book.size price sequence order value
@[pf_inline] def Book.insert (book : Book)
    (price sequence owner size lastSlot lastTime : UInt64) : UInt64 :=
  insertOrderedPair book.map price sequence owner size lastSlot lastTime
@[pf_inline] def Book.remove (book : Book) (price sequence : UInt64) : UInt64 :=
  removeOrderedPair book.map price sequence

def Layout.wellFormed (layout : Layout) : Bool :=
  layout.account > 0 && layout.accountBytes > 0 &&
    layout.bids.wellFormed && layout.asks.wellFormed && layout.traders.map.wellFormed &&
    layout.header.status.wellFormed && layout.header.marketSequence.wellFormed &&
    layout.header.baseLotSize.wellFormed && layout.header.quoteLotSize.wellFormed &&
    layout.header.baseLotsPerBaseUnit.wellFormed && layout.header.tickSize.wellFormed &&
    layout.header.orderSequence.wellFormed && layout.header.takerFeeBps.wellFormed &&
    layout.header.collectedQuoteFees.wellFormed && layout.header.unclaimedQuoteFees.wellFormed &&
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
@[pf_inline] def Layout.takerFeeBps (layout : Layout) : UInt64 :=
  read layout.header.takerFeeBps 0
@[pf_inline] def Layout.unclaimedQuoteFees (layout : Layout) : UInt64 :=
  read layout.header.unclaimedQuoteFees 0

@[pf_inline] def Layout.bidSize (layout : Layout) : UInt64 := layout.bids.count
@[pf_inline] def Layout.askSize (layout : Layout) : UInt64 := layout.asks.count

@[pf_inline] def Layout.tradersValid (layout : Layout) : UInt64 :=
  validate layout.traders.map
@[pf_inline] def Layout.bidsValid (layout : Layout) : UInt64 :=
  layout.bids.validate
@[pf_inline] def Layout.asksValid (layout : Layout) : UInt64 :=
  layout.asks.validate

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

@[pf_inline] def Layout.traderKey0 (layout : Layout) (trader : UInt64) : UInt64 :=
  key4Word0 layout.traders.map trader
@[pf_inline] def Layout.traderKey1 (layout : Layout) (trader : UInt64) : UInt64 :=
  key4Word1 layout.traders.map trader
@[pf_inline] def Layout.traderKey2 (layout : Layout) (trader : UInt64) : UInt64 :=
  key4Word2 layout.traders.map trader
@[pf_inline] def Layout.traderKey3 (layout : Layout) (trader : UInt64) : UInt64 :=
  key4Word3 layout.traders.map trader

@[pf_inline] def Layout.findBid (layout : Layout) (price sequence : UInt64) : UInt64 :=
  layout.bids.find price sequence

@[pf_inline] def Layout.findAsk (layout : Layout) (price sequence : UInt64) : UInt64 :=
  layout.asks.find price sequence

@[pf_inline] def Layout.insertBid (layout : Layout)
    (price sequence owner size lastSlot lastTime : UInt64) : UInt64 :=
  layout.bids.insert price sequence owner size lastSlot lastTime

@[pf_inline] def Layout.insertAsk (layout : Layout)
    (price sequence owner size lastSlot lastTime : UInt64) : UInt64 :=
  layout.asks.insert price sequence owner size lastSlot lastTime

@[pf_inline] def Layout.removeBid (layout : Layout) (price sequence : UInt64) : UInt64 :=
  layout.bids.remove price sequence
@[pf_inline] def Layout.removeAsk (layout : Layout) (price sequence : UInt64) : UInt64 :=
  layout.asks.remove price sequence

@[pf_inline] def Layout.bidOwner (layout : Layout) (order : UInt64) : UInt64 :=
  layout.bids.ownerAt order
@[pf_inline] def Layout.bidOrderSize (layout : Layout) (order : UInt64) : UInt64 :=
  layout.bids.sizeAt order
@[pf_inline] def Layout.askOwner (layout : Layout) (order : UInt64) : UInt64 :=
  layout.asks.ownerAt order
@[pf_inline] def Layout.askOrderSize (layout : Layout) (order : UInt64) : UInt64 :=
  layout.asks.sizeAt order

@[pf_inline] def Layout.setBidOrderSize (layout : Layout) (order value : UInt64) : UInt64 :=
  layout.bids.setSizeAt order value
@[pf_inline] def Layout.setAskOrderSize (layout : Layout) (order value : UInt64) : UInt64 :=
  layout.asks.setSizeAt order value
@[pf_inline] def Layout.setBidOrderSizeOrRemove (layout : Layout)
    (order price sequence value : UInt64) : UInt64 :=
  layout.bids.setSizeOrRemove order price sequence value
@[pf_inline] def Layout.setAskOrderSizeOrRemove (layout : Layout)
    (order price sequence value : UInt64) : UInt64 :=
  layout.asks.setSizeOrRemove order price sequence value

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

@[pf_inline] def Layout.setUnclaimedQuoteFees (layout : Layout) (value : UInt64) : UInt64 :=
  write layout.header.unclaimedQuoteFees 0 value

end Examples.Svm.PhoenixV1
