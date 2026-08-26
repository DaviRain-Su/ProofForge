import ProofForge

/-!
Phoenix v1 market-account profile gate.

The official program does not accept arbitrary runtime capacities. Its 24-byte `MarketSizeParams`
header selects one of twelve statically compiled `FIFOMarket<Pubkey, B, A, S>` layouts. This module
validates that dispatch boundary, fixed scalar/allocator metadata, and both complete order trees
plus allocator partitions against the pinned Sokoban 0.3.0 layout.

This is deliberately a separate verifier program whose ProofForge state is account 0 and candidate
Phoenix market is account 1. It does not yet claim trader traversal or official instruction execution.
-/
namespace Projects.PhoenixV1Profile

open ProofForge.Svm.Runtime

def phoenixProgramOwner0 : UInt64 := 11497730047637682189
def phoenixProgramOwner1 : UInt64 := 2178672117088209453
def phoenixProgramOwner2 : UInt64 := 16206118848139790065
def phoenixProgramOwner3 : UInt64 := 1630085884070697098

def marketHeaderDiscriminant : UInt64 := 8167313896524341111
def marketHeaderBytes : UInt64 := 576

/-- Full account bytes: 576-byte header + `400 + 64 * (bids + asks) + 144 * seats` body. -/
def accountBytesFor (bids asks seats : UInt64) : UInt64 :=
  if bids = 512 && asks = 512 &&
      (seats = 128 || seats = 1025 || seats = 1153) then
    976 + 64 * (bids + asks) + 144 * seats
  else if bids = 1024 && asks = 1024 &&
      (seats = 128 || seats = 2049 || seats = 2177) then
    976 + 64 * (bids + asks) + 144 * seats
  else if bids = 2048 && asks = 2048 &&
      (seats = 128 || seats = 4097 || seats = 4225) then
    976 + 64 * (bids + asks) + 144 * seats
  else if bids = 4096 && asks = 4096 &&
      (seats = 128 || seats = 8193 || seats = 8321) then
    976 + 64 * (bids + asks) + 144 * seats
  else
    0

/-- Sum account-resident tree sizes only when each allocator size fits its compiled capacity.
Zero is both the valid empty-market result and the fail-closed malformed-metadata result. -/
def boundedBodyEntryCount (bookCapacity seats bidCount askCount traderCount : UInt64) : UInt64 :=
  if bidCount ≤ bookCapacity && askCount ≤ bookCapacity && traderCount ≤ seats then
    bidCount + askCount + traderCount
  else
    0

def lowUInt32 (word : UInt64) : UInt64 := word &&& 0xffffffff

def highUInt32 (word : UInt64) : UInt64 := word >>> 32

/-- Validate the account-resident Sokoban allocator envelope without dereferencing a node.
Indexes are one-based; zero is only the empty-tree sentinel, and `bumpIndex` is the next unused
index rather than a dereferenceable node. Padding must retain its canonical zero value. -/
def allocatorHeaderValid (capacity size rootWord paddingWord cursorWord : UInt64) : Bool :=
  let root := lowUInt32 rootWord
  let bumpIndex := lowUInt32 cursorWord
  let freeListHead := highUInt32 cursorWord
  highUInt32 rootWord = 0 && paddingWord = 0 &&
    size ≤ capacity && 1 ≤ bumpIndex && bumpIndex ≤ capacity + 1 && size < bumpIndex &&
    1 ≤ freeListHead && freeListHead ≤ bumpIndex &&
    (if size = 0 then root = 0 else 1 ≤ root && root < bumpIndex && root ≤ capacity)

def threeAllocatorHeadersValid (bookCapacity seats : UInt64)
    (bidRoot bidPadding bidSize bidCursor : UInt64)
    (askRoot askPadding askSize askCursor : UInt64)
    (traderRoot traderPadding traderSize traderCursor : UInt64) : UInt64 :=
  if allocatorHeaderValid bookCapacity bidSize bidRoot bidPadding bidCursor &&
      allocatorHeaderValid bookCapacity askSize askRoot askPadding askCursor &&
      allocatorHeaderValid seats traderSize traderRoot traderPadding traderCursor then
    1
  else
    0

def nodeIndexOrNullValid (capacity bumpIndex index : UInt64) : Bool :=
  index = 0 || (1 ≤ index && index < bumpIndex && index ≤ capacity)

/-- Validate the fields that can be checked from one bid root slot without traversing the tree. -/
def boundedBidRootPrice
    (capacity bumpIndex links parentAndColor price : UInt64) : UInt64 :=
  if parentAndColor = 0 &&
      nodeIndexOrNullValid capacity bumpIndex (lowUInt32 links) &&
      nodeIndexOrNullValid capacity bumpIndex (highUInt32 links) then
    price
  else
    0

def boundedNodeSlot (capacity index : UInt64) : UInt64 :=
  if 1 ≤ index && index ≤ capacity then index - 1 else 0

def bidKeyBefore
    (lhsPrice lhsSequence rhsPrice rhsSequence : UInt64) : Bool :=
  lhsPrice > rhsPrice || (lhsPrice = rhsPrice && lhsSequence > rhsSequence)

def boundedBidChildValid
    (capacity bumpIndex root child links parentAndColor sequence : UInt64) : Bool :=
  child = 0 ||
    (nodeIndexOrNullValid capacity bumpIndex child && child ≠ root &&
      lowUInt32 parentAndColor = root && highUInt32 parentAndColor ≤ 1 &&
      sequence >>> 63 = 1 &&
      nodeIndexOrNullValid capacity bumpIndex (lowUInt32 links) &&
      nodeIndexOrNullValid capacity bumpIndex (highUInt32 links))

/-- Validate the root and both immediate bid children from account-resident node words. This is an
O(1)-memory neighborhood check, not a whole-tree traversal or allocator-membership proof. -/
def boundedBidRootNeighborhoodValid
    (capacity bumpIndex root rootLinks rootParentAndColor rootPrice rootSequence : UInt64)
    (leftLinks leftParentAndColor leftPrice leftSequence : UInt64)
    (rightLinks rightParentAndColor rightPrice rightSequence : UInt64) : UInt64 :=
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  if rootParentAndColor = 0 && rootSequence >>> 63 = 1 &&
      nodeIndexOrNullValid capacity bumpIndex left &&
      nodeIndexOrNullValid capacity bumpIndex right &&
      boundedBidChildValid capacity bumpIndex root left
        leftLinks leftParentAndColor leftSequence &&
      boundedBidChildValid capacity bumpIndex root right
        rightLinks rightParentAndColor rightSequence &&
      (left = 0 || bidKeyBefore leftPrice leftSequence rootPrice rootSequence) &&
      (right = 0 || bidKeyBefore rootPrice rootSequence rightPrice rightSequence) then
    1
  else
    0

private def bidRootNeighborhood512 (root bumpIndex : UInt64) : UInt64 :=
  let rootSlot := root - 1
  let rootLinks := accDataWordAt 1 114 8 512 rootSlot
  let rootParentAndColor := accDataWordAt 1 115 8 512 rootSlot
  let rootPrice := accDataWordAt 1 116 8 512 rootSlot
  let rootSequence := accDataWordAt 1 117 8 512 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 512 left
  let rightSlot := boundedNodeSlot 512 right
  boundedBidRootNeighborhoodValid 512 bumpIndex root
    rootLinks rootParentAndColor rootPrice rootSequence
    (accDataWordAt 1 114 8 512 leftSlot)
    (accDataWordAt 1 115 8 512 leftSlot)
    (accDataWordAt 1 116 8 512 leftSlot)
    (accDataWordAt 1 117 8 512 leftSlot)
    (accDataWordAt 1 114 8 512 rightSlot)
    (accDataWordAt 1 115 8 512 rightSlot)
    (accDataWordAt 1 116 8 512 rightSlot)
    (accDataWordAt 1 117 8 512 rightSlot)

private def bidRootNeighborhood1024 (root bumpIndex : UInt64) : UInt64 :=
  let rootSlot := root - 1
  let rootLinks := accDataWordAt 1 114 8 1024 rootSlot
  let rootParentAndColor := accDataWordAt 1 115 8 1024 rootSlot
  let rootPrice := accDataWordAt 1 116 8 1024 rootSlot
  let rootSequence := accDataWordAt 1 117 8 1024 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 1024 left
  let rightSlot := boundedNodeSlot 1024 right
  boundedBidRootNeighborhoodValid 1024 bumpIndex root
    rootLinks rootParentAndColor rootPrice rootSequence
    (accDataWordAt 1 114 8 1024 leftSlot)
    (accDataWordAt 1 115 8 1024 leftSlot)
    (accDataWordAt 1 116 8 1024 leftSlot)
    (accDataWordAt 1 117 8 1024 leftSlot)
    (accDataWordAt 1 114 8 1024 rightSlot)
    (accDataWordAt 1 115 8 1024 rightSlot)
    (accDataWordAt 1 116 8 1024 rightSlot)
    (accDataWordAt 1 117 8 1024 rightSlot)

private def bidRootNeighborhood2048 (root bumpIndex : UInt64) : UInt64 :=
  let rootSlot := root - 1
  let rootLinks := accDataWordAt 1 114 8 2048 rootSlot
  let rootParentAndColor := accDataWordAt 1 115 8 2048 rootSlot
  let rootPrice := accDataWordAt 1 116 8 2048 rootSlot
  let rootSequence := accDataWordAt 1 117 8 2048 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 2048 left
  let rightSlot := boundedNodeSlot 2048 right
  boundedBidRootNeighborhoodValid 2048 bumpIndex root
    rootLinks rootParentAndColor rootPrice rootSequence
    (accDataWordAt 1 114 8 2048 leftSlot)
    (accDataWordAt 1 115 8 2048 leftSlot)
    (accDataWordAt 1 116 8 2048 leftSlot)
    (accDataWordAt 1 117 8 2048 leftSlot)
    (accDataWordAt 1 114 8 2048 rightSlot)
    (accDataWordAt 1 115 8 2048 rightSlot)
    (accDataWordAt 1 116 8 2048 rightSlot)
    (accDataWordAt 1 117 8 2048 rightSlot)

private def bidRootNeighborhood4096 (root bumpIndex : UInt64) : UInt64 :=
  let rootSlot := root - 1
  let rootLinks := accDataWordAt 1 114 8 4096 rootSlot
  let rootParentAndColor := accDataWordAt 1 115 8 4096 rootSlot
  let rootPrice := accDataWordAt 1 116 8 4096 rootSlot
  let rootSequence := accDataWordAt 1 117 8 4096 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 4096 left
  let rightSlot := boundedNodeSlot 4096 right
  boundedBidRootNeighborhoodValid 4096 bumpIndex root
    rootLinks rootParentAndColor rootPrice rootSequence
    (accDataWordAt 1 114 8 4096 leftSlot)
    (accDataWordAt 1 115 8 4096 leftSlot)
    (accDataWordAt 1 116 8 4096 leftSlot)
    (accDataWordAt 1 117 8 4096 leftSlot)
    (accDataWordAt 1 114 8 4096 rightSlot)
    (accDataWordAt 1 115 8 4096 rightSlot)
    (accDataWordAt 1 116 8 4096 rightSlot)
    (accDataWordAt 1 117 8 4096 rightSlot)

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then .ok ({ dummy := 0 }, 0) else .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 := 0

/-- Return the exact selected profile size, or zero when account 1 is not a canonical Phoenix-v1
market account. Header words are read only after the generic data-length gate proves 576 bytes. -/
@[pf_entry]
def profileAccountBytes (_s : State) : UInt64 :=
  if accDataLen 1 < marketHeaderBytes then
    0
  else
    let bids := accDataWord 1 2
    let asks := accDataWord 1 3
    let seats := accDataWord 1 4
    let expected := accountBytesFor bids asks seats
    if accOwnerWord 1 0 = phoenixProgramOwner0 &&
        accOwnerWord 1 1 = phoenixProgramOwner1 &&
        accOwnerWord 1 2 = phoenixProgramOwner2 &&
        accOwnerWord 1 3 = phoenixProgramOwner3 &&
        accDataWord 1 0 = marketHeaderDiscriminant &&
        expected ≠ 0 && accDataLen 1 = expected then
      expected
    else
      0

/-- Return the Phoenix market sequence scalar at absolute account word 106. The body starts after
the 576-byte header and its first 32 words are padding, so this offset is profile-independent. -/
@[pf_entry]
def marketSequence (s : State) : UInt64 :=
  if profileAccountBytes s = 0 then 0 else accDataWord 1 106

/--
Read only the three account-resident Sokoban allocator `size` words. The bid allocator starts at
absolute word 112. Ask/trader offsets are selected from four compile-time layouts; the seat count
does not move either tree, and only bounds the trader allocator size. No heap object, dynamic map,
runtime offset, or node array is constructed.
-/
@[pf_entry]
def bodyEntryCount (s : State) : UInt64 :=
  if profileAccountBytes s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let seats := accDataWord 1 4
    let bidCount := accDataWord 1 112
    if bids = 512 then
      boundedBodyEntryCount 512 seats bidCount (accDataWord 1 4212) (accDataWord 1 8312)
    else if bids = 1024 then
      boundedBodyEntryCount 1024 seats bidCount (accDataWord 1 8308) (accDataWord 1 16504)
    else if bids = 2048 then
      boundedBodyEntryCount 2048 seats bidCount (accDataWord 1 16500) (accDataWord 1 32888)
    else if bids = 4096 then
      boundedBodyEntryCount 4096 seats bidCount (accDataWord 1 32884) (accDataWord 1 65656)
    else
      0

/--
Validate the fixed tree headers before any future node reader follows `root`, child, or free-list
indexes. Each profile selects literal account words for the three headers. This reads the packed
u32 metadata in place; it does not allocate, copy nodes, or calculate a runtime data offset.
-/
@[pf_entry]
def allocatorHeadersValid (s : State) : UInt64 :=
  if profileAccountBytes s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let seats := accDataWord 1 4
    if bids = 512 then
      threeAllocatorHeadersValid 512 seats
        (accDataWord 1 110) (accDataWord 1 111) (accDataWord 1 112) (accDataWord 1 113)
        (accDataWord 1 4210) (accDataWord 1 4211) (accDataWord 1 4212) (accDataWord 1 4213)
        (accDataWord 1 8310) (accDataWord 1 8311) (accDataWord 1 8312) (accDataWord 1 8313)
    else if bids = 1024 then
      threeAllocatorHeadersValid 1024 seats
        (accDataWord 1 110) (accDataWord 1 111) (accDataWord 1 112) (accDataWord 1 113)
        (accDataWord 1 8306) (accDataWord 1 8307) (accDataWord 1 8308) (accDataWord 1 8309)
        (accDataWord 1 16502) (accDataWord 1 16503) (accDataWord 1 16504) (accDataWord 1 16505)
    else if bids = 2048 then
      threeAllocatorHeadersValid 2048 seats
        (accDataWord 1 110) (accDataWord 1 111) (accDataWord 1 112) (accDataWord 1 113)
        (accDataWord 1 16498) (accDataWord 1 16499) (accDataWord 1 16500) (accDataWord 1 16501)
        (accDataWord 1 32886) (accDataWord 1 32887) (accDataWord 1 32888) (accDataWord 1 32889)
    else if bids = 4096 then
      threeAllocatorHeadersValid 4096 seats
        (accDataWord 1 110) (accDataWord 1 111) (accDataWord 1 112) (accDataWord 1 113)
        (accDataWord 1 32882) (accDataWord 1 32883) (accDataWord 1 32884) (accDataWord 1 32885)
        (accDataWord 1 65654) (accDataWord 1 65655) (accDataWord 1 65656) (accDataWord 1 65657)
    else
      0

/--
Read the bid root's price directly from its account-resident 64-byte Sokoban slot. The root index
is converted from one-based to zero-based only after `allocatorHeadersValid`; each profile then
selects a compile-time fixed base/stride/capacity for `accDataWordAt`. Root parent/color and direct
child index ranges are validated, but this does not yet traverse the tree or classify free slots.
-/
@[pf_entry]
def bidRootPrice (s : State) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let root := lowUInt32 (accDataWord 1 110)
    let bumpIndex := lowUInt32 (accDataWord 1 113)
    if root = 0 then
      0
    else if bids = 512 then
      boundedBidRootPrice 512 bumpIndex
        (accDataWordAt 1 114 8 512 (root - 1))
        (accDataWordAt 1 115 8 512 (root - 1))
        (accDataWordAt 1 116 8 512 (root - 1))
    else if bids = 1024 then
      boundedBidRootPrice 1024 bumpIndex
        (accDataWordAt 1 114 8 1024 (root - 1))
        (accDataWordAt 1 115 8 1024 (root - 1))
        (accDataWordAt 1 116 8 1024 (root - 1))
    else if bids = 2048 then
      boundedBidRootPrice 2048 bumpIndex
        (accDataWordAt 1 114 8 2048 (root - 1))
        (accDataWordAt 1 115 8 2048 (root - 1))
        (accDataWordAt 1 116 8 2048 (root - 1))
    else if bids = 4096 then
      boundedBidRootPrice 4096 bumpIndex
        (accDataWordAt 1 114 8 4096 (root - 1))
        (accDataWordAt 1 115 8 4096 (root - 1))
        (accDataWordAt 1 116 8 4096 (root - 1))
    else
      0

/--
Validate the bid root plus both immediate child records in place. Child reads use a clamped slot
only to keep malformed/null indexes inside the statically bounded reader; the original indexes are
still checked and any malformed relation returns zero. This does not traverse descendants.
-/
@[pf_entry]
def bidRootNeighborhoodValid (s : State) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let root := lowUInt32 (accDataWord 1 110)
    let bumpIndex := lowUInt32 (accDataWord 1 113)
    if root = 0 then
      1
    else if bids = 512 then
      bidRootNeighborhood512 root bumpIndex
    else if bids = 1024 then
      bidRootNeighborhood1024 root bumpIndex
    else if bids = 2048 then
      bidRootNeighborhood2048 root bumpIndex
    else if bids = 4096 then
      bidRootNeighborhood4096 root bumpIndex
    else
      0

/--
Validate one caller-selected bid node's parent path in account-resident storage. The emitted loop
keeps only current index and depth, validates each parent/color word and parent→child reciprocal
edge, and must reach the canonical root in at most 32 edges. A valid red-black tree with at most
4096 nodes has height below this bound. This proves one path, not whole-tree coverage or live/free
partition membership.
-/
@[pf_entry]
def bidParentPathValid (s : State) (index : UInt64) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let root := lowUInt32 (accDataWord 1 110)
    let bumpIndex := lowUInt32 (accDataWord 1 113)
    if root = 0 then
      if index = 0 then 1 else 0
    else if bids = 512 then
      accDataParentPathValid 1 114 115 8 512 32 index root bumpIndex
    else if bids = 1024 then
      accDataParentPathValid 1 114 115 8 1024 32 index root bumpIndex
    else if bids = 2048 then
      accDataParentPathValid 1 114 115 8 2048 32 index root bumpIndex
    else if bids = 4096 then
      accDataParentPathValid 1 114 115 8 4096 32 index root bumpIndex
    else
      0

/--
Validate the complete bid red-black tree and the bid allocator's free list in account-resident
storage. The emitted iterative traversal enforces reciprocal links, red/black rules, equal black
height, strict Phoenix bid FIFO ordering, exact live size, and an exact disjoint partition of every
slot below `bumpIndex`. It uses a fixed 4096-bit stack bitmap and never allocates or copies nodes.
-/
@[pf_entry]
def bidTreeValid (s : State) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let root := lowUInt32 (accDataWord 1 110)
    let size := accDataWord 1 112
    let cursor := accDataWord 1 113
    let bumpIndex := lowUInt32 cursor
    let freeListHead := highUInt32 cursor
    if bids = 512 then
      accDataRbTreeValid 1 114 115 116 117 8 512 1
        root size bumpIndex freeListHead
    else if bids = 1024 then
      accDataRbTreeValid 1 114 115 116 117 8 1024 1
        root size bumpIndex freeListHead
    else if bids = 2048 then
      accDataRbTreeValid 1 114 115 116 117 8 2048 1
        root size bumpIndex freeListHead
    else if bids = 4096 then
      accDataRbTreeValid 1 114 115 116 117 8 4096 1
        root size bumpIndex freeListHead
    else
      0

/--
Validate the complete ask red-black tree and its allocator partition. This is the same fixed-memory
account walk as `bidTreeValid`, with Phoenix ask keys required to be side-tag 0 and strictly
ascending by `(price, sequence)`.
-/
@[pf_entry]
def askTreeValid (s : State) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    if bids = 512 then
      let cursor := accDataWord 1 4213
      accDataRbTreeValid 1 4214 4215 4216 4217 8 512 0
        (lowUInt32 (accDataWord 1 4210)) (accDataWord 1 4212)
        (lowUInt32 cursor) (highUInt32 cursor)
    else if bids = 1024 then
      let cursor := accDataWord 1 8309
      accDataRbTreeValid 1 8310 8311 8312 8313 8 1024 0
        (lowUInt32 (accDataWord 1 8306)) (accDataWord 1 8308)
        (lowUInt32 cursor) (highUInt32 cursor)
    else if bids = 2048 then
      let cursor := accDataWord 1 16501
      accDataRbTreeValid 1 16502 16503 16504 16505 8 2048 0
        (lowUInt32 (accDataWord 1 16498)) (accDataWord 1 16500)
        (lowUInt32 cursor) (highUInt32 cursor)
    else if bids = 4096 then
      let cursor := accDataWord 1 32885
      accDataRbTreeValid 1 32886 32887 32888 32889 8 4096 0
        (lowUInt32 (accDataWord 1 32882)) (accDataWord 1 32884)
        (lowUInt32 cursor) (highUInt32 cursor)
    else
      0

/-- Direct boundary probe used to prove a short account fails before reading bytes 32..39. -/
@[pf_entry]
def headerSeats (_s : State) : UInt64 :=
  accDataWord 1 4

attribute [pf_inline] accountBytesFor boundedBodyEntryCount lowUInt32 highUInt32
  allocatorHeaderValid threeAllocatorHeadersValid nodeIndexOrNullValid boundedBidRootPrice
  boundedNodeSlot bidKeyBefore boundedBidChildValid boundedBidRootNeighborhoodValid
  bidRootNeighborhood512 bidRootNeighborhood1024 bidRootNeighborhood2048
  bidRootNeighborhood4096 profileAccountBytes allocatorHeadersValid

end Projects.PhoenixV1Profile
