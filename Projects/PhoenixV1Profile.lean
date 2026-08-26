import ProofForge

/-!
Phoenix v1 market-account profile gate.

The official program does not accept arbitrary runtime capacities. Its 24-byte `MarketSizeParams`
header selects one of twelve statically compiled `FIFOMarket<Pubkey, B, A, S>` layouts. This module
validates that dispatch boundary, fixed scalar/allocator metadata, and all three complete trees
plus allocator partitions against the pinned Sokoban 0.3.0 layout.

This is deliberately a separate verifier/profile program. Generated probes keep ProofForge state in
account 0 and the candidate market in account 1; the official raw adapter instead authenticates a
physical program prefix and mutates the market in account 2. Its fixed-shape Sokoban routines are
composed through bounded target-owned components; official instruction coverage currently includes
tags 4–7 (`ReduceOrder`, `ReduceOrderWithFreeFunds`, `CancelAllOrders`, and
`CancelAllOrdersWithFreeFunds`), not the complete Phoenix instruction set.
-/
namespace Projects.PhoenixV1Profile

open ProofForge.Svm.Runtime

def phoenixProgramOwner0 : UInt64 := 11497730047637682189
def phoenixProgramOwner1 : UInt64 := 2178672117088209453
def phoenixProgramOwner2 : UInt64 := 16206118848139790065
def phoenixProgramOwner3 : UInt64 := 1630085884070697098

def splTokenProgram0 : UInt64 := 10637895772709248262
def splTokenProgram1 : UInt64 := 12428223917890587609
def splTokenProgram2 : UInt64 := 10463932726783620124
def splTokenProgram3 : UInt64 := 12178014311288245306

def marketHeaderDiscriminant : UInt64 := 8167313896524341111
def marketHeaderBytes : UInt64 := 576
def u64Max : UInt64 := 0xffffffffffffffff

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

def packUInt32 (low high : UInt64) : UInt64 := low ||| (high <<< 32)

/-- Compare four little-endian account limbs in the original 32-byte key order. The compact SVM
byte-swap intrinsic makes each unsigned limb comparison match Rust `[u8; 32]` lexicographic Ord. -/
def key4Before
    (lhs0 lhs1 lhs2 lhs3 rhs0 rhs1 rhs2 rhs3 : UInt64) : Bool :=
  let lhs0 := svmByteSwap64 lhs0
  let lhs1 := svmByteSwap64 lhs1
  let lhs2 := svmByteSwap64 lhs2
  let lhs3 := svmByteSwap64 lhs3
  let rhs0 := svmByteSwap64 rhs0
  let rhs1 := svmByteSwap64 rhs1
  let rhs2 := svmByteSwap64 rhs2
  let rhs3 := svmByteSwap64 rhs3
  lhs0 < rhs0 || (lhs0 = rhs0 &&
    (lhs1 < rhs1 || (lhs1 = rhs1 &&
      (lhs2 < rhs2 || (lhs2 = rhs2 && lhs3 < rhs3)))))

def key4Equal
    (lhs0 lhs1 lhs2 lhs3 rhs0 rhs1 rhs2 rhs3 : UInt64) : Bool :=
  lhs0 = rhs0 && lhs1 = rhs1 && lhs2 = rhs2 && lhs3 = rhs3

def splTokenProgramValidAt (account : UInt64) : UInt64 :=
  if isExecutable account = 1 &&
    key4Equal
      (accKeyWord account 0) (accKeyWord account 1)
      (accKeyWord account 2) (accKeyWord account 3)
      splTokenProgram0 splTokenProgram1 splTokenProgram2 splTokenProgram3 then 1 else 0

def reduceStatusValidAt (marketAccount : UInt64) : UInt64 :=
  let status := accDataWord marketAccount 1
  if 1 ≤ status && status ≤ 4 then 1 else 0

/-- Canonical final topology selectors for third insertion cases: 1=LL, 2=LR,
3=left-child/no-fix, 4=RR, 5=RL, 6=right-child/no-fix. -/
def thirdRoot (caseTag : UInt64) : UInt64 :=
  if caseTag = 1 || caseTag = 4 then 2
  else if caseTag = 2 || caseTag = 5 then 3
  else 1

def thirdNode1Links (caseTag : UInt64) : UInt64 :=
  if caseTag = 3 then 0x0000000300000002
  else if caseTag = 6 then 0x0000000200000003
  else 0

def thirdNode1ParentColor (caseTag : UInt64) : UInt64 :=
  if caseTag = 1 || caseTag = 4 then 0x0000000100000002
  else if caseTag = 2 || caseTag = 5 then 0x0000000100000003
  else 0

def thirdNode2Links (caseTag : UInt64) : UInt64 :=
  if caseTag = 1 then 0x0000000100000003
  else if caseTag = 4 then 0x0000000300000001
  else 0

def thirdNode2ParentColor (caseTag : UInt64) : UInt64 :=
  if caseTag = 2 || caseTag = 5 then 0x0000000100000003
  else if caseTag = 3 || caseTag = 6 then 0x0000000100000001
  else 0

def thirdNode3Links (caseTag : UInt64) : UInt64 :=
  if caseTag = 2 then 0x0000000100000002
  else if caseTag = 5 then 0x0000000200000001
  else 0

def thirdNode3ParentColor (caseTag : UInt64) : UInt64 :=
  if caseTag = 1 || caseTag = 4 then 0x0000000100000002
  else if caseTag = 3 || caseTag = 6 then 0x0000000100000001
  else 0

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

/-- Return the exact selected profile size, or zero when `marketAccount` is not a canonical
Phoenix-v1 market. The account index must become a literal through `pf_inline`; no runtime account
selection or geometry is introduced. -/
def profileAccountBytesAt (marketAccount : UInt64) : UInt64 :=
  if accDataLen marketAccount < marketHeaderBytes then
    0
  else
    let bids := accDataWord marketAccount 2
    let asks := accDataWord marketAccount 3
    let seats := accDataWord marketAccount 4
    let expected := accountBytesFor bids asks seats
    if accOwnerWord marketAccount 0 = phoenixProgramOwner0 &&
        accOwnerWord marketAccount 1 = phoenixProgramOwner1 &&
        accOwnerWord marketAccount 2 = phoenixProgramOwner2 &&
        accOwnerWord marketAccount 3 = phoenixProgramOwner3 &&
        accDataWord marketAccount 0 = marketHeaderDiscriminant &&
        expected ≠ 0 && accDataLen marketAccount = expected then
      expected
    else
      0

/-- Generated verifier adapter for the historical state/market account geometry. -/
@[pf_entry]
def profileAccountBytes (_s : State) : UInt64 :=
  profileAccountBytesAt 1

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

/-- Validate all three fixed allocator headers on one compile-time-selected market account. -/
def allocatorHeadersValidAt (marketAccount : UInt64) : UInt64 :=
  if profileAccountBytesAt marketAccount = 0 then
    0
  else
    let bids := accDataWord marketAccount 2
    let seats := accDataWord marketAccount 4
    if bids = 512 then
      threeAllocatorHeadersValid 512 seats
        (accDataWord marketAccount 110) (accDataWord marketAccount 111)
        (accDataWord marketAccount 112) (accDataWord marketAccount 113)
        (accDataWord marketAccount 4210) (accDataWord marketAccount 4211)
        (accDataWord marketAccount 4212) (accDataWord marketAccount 4213)
        (accDataWord marketAccount 8310) (accDataWord marketAccount 8311)
        (accDataWord marketAccount 8312) (accDataWord marketAccount 8313)
    else if bids = 1024 then
      threeAllocatorHeadersValid 1024 seats
        (accDataWord marketAccount 110) (accDataWord marketAccount 111)
        (accDataWord marketAccount 112) (accDataWord marketAccount 113)
        (accDataWord marketAccount 8306) (accDataWord marketAccount 8307)
        (accDataWord marketAccount 8308) (accDataWord marketAccount 8309)
        (accDataWord marketAccount 16502) (accDataWord marketAccount 16503)
        (accDataWord marketAccount 16504) (accDataWord marketAccount 16505)
    else if bids = 2048 then
      threeAllocatorHeadersValid 2048 seats
        (accDataWord marketAccount 110) (accDataWord marketAccount 111)
        (accDataWord marketAccount 112) (accDataWord marketAccount 113)
        (accDataWord marketAccount 16498) (accDataWord marketAccount 16499)
        (accDataWord marketAccount 16500) (accDataWord marketAccount 16501)
        (accDataWord marketAccount 32886) (accDataWord marketAccount 32887)
        (accDataWord marketAccount 32888) (accDataWord marketAccount 32889)
    else if bids = 4096 then
      threeAllocatorHeadersValid 4096 seats
        (accDataWord marketAccount 110) (accDataWord marketAccount 111)
        (accDataWord marketAccount 112) (accDataWord marketAccount 113)
        (accDataWord marketAccount 32882) (accDataWord marketAccount 32883)
        (accDataWord marketAccount 32884) (accDataWord marketAccount 32885)
        (accDataWord marketAccount 65654) (accDataWord marketAccount 65655)
        (accDataWord marketAccount 65656) (accDataWord marketAccount 65657)
    else
      0

/-- Generated verifier adapter for account 1. -/
@[pf_entry]
def allocatorHeadersValid (_s : State) : UInt64 :=
  allocatorHeadersValidAt 1

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

/--
Validate the complete registered-trader red-black tree and allocator partition directly in the
Phoenix account. Trader keys are 32-byte Pubkeys ordered by Rust `[u8; 32]` lexicographic order,
not four little-endian integer limbs. Each of the twelve official `(book, seats)` profiles selects
literal node bases, 18-word stride, and capacity. The emitted traversal uses only a fixed bitmap
and fixed-depth stack; it never creates a heap Map or stores pointers in account data.
-/
@[pf_entry]
def traderTreeValid (s : State) : UInt64 :=
  if profileAccountBytes s = 0 || allocatorHeadersValid s = 0 then
    0
  else
    let bids := accDataWord 1 2
    let seats := accDataWord 1 4
    if bids = 512 then
      let cursor := accDataWord 1 8313
      let root := lowUInt32 (accDataWord 1 8310)
      let size := accDataWord 1 8312
      if seats = 128 then
        accDataRbTreeKey4Valid 1 8314 8315 8316 18 128
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 1025 then
        accDataRbTreeKey4Valid 1 8314 8315 8316 18 1025
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 1153 then
        accDataRbTreeKey4Valid 1 8314 8315 8316 18 1153
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else
        0
    else if bids = 1024 then
      let cursor := accDataWord 1 16505
      let root := lowUInt32 (accDataWord 1 16502)
      let size := accDataWord 1 16504
      if seats = 128 then
        accDataRbTreeKey4Valid 1 16506 16507 16508 18 128
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 2049 then
        accDataRbTreeKey4Valid 1 16506 16507 16508 18 2049
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 2177 then
        accDataRbTreeKey4Valid 1 16506 16507 16508 18 2177
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else
        0
    else if bids = 2048 then
      let cursor := accDataWord 1 32889
      let root := lowUInt32 (accDataWord 1 32886)
      let size := accDataWord 1 32888
      if seats = 128 then
        accDataRbTreeKey4Valid 1 32890 32891 32892 18 128
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 4097 then
        accDataRbTreeKey4Valid 1 32890 32891 32892 18 4097
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 4225 then
        accDataRbTreeKey4Valid 1 32890 32891 32892 18 4225
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else
        0
    else if bids = 4096 then
      let cursor := accDataWord 1 65657
      let root := lowUInt32 (accDataWord 1 65654)
      let size := accDataWord 1 65656
      if seats = 128 then
        accDataRbTreeKey4Valid 1 65658 65659 65660 18 128
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 8193 then
        accDataRbTreeKey4Valid 1 65658 65659 65660 18 8193
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else if seats = 8321 then
        accDataRbTreeKey4Valid 1 65658 65659 65660 18 8321
          root size (lowUInt32 cursor) (highUInt32 cursor)
      else
        0
    else
      0

/-- Return the one-based trader slot for one 32-byte Pubkey key in the smallest official profile,
or zero when absent/invalid. Complete tree/free-list validation runs before bounded search. -/
@[pf_entry]
def findTrader128 (s : State) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let cursor := accDataWord 1 8313
    let valid := accDataRbTreeKey4Valid 1 8314 8315 8316 18 128
      (lowUInt32 (accDataWord 1 8310)) (accDataWord 1 8312)
      (lowUInt32 cursor) (highUInt32 cursor)
    if valid = 1 then
      accDataRbTreeKey4Find 1 8310 8314 8315 8316 18 128 key0 key1 key2 key3
    else
      0
  else
    0

/-- Return the one-based bid slot for an exact Phoenix FIFO key in the 512-node profile. -/
@[pf_entry]
def findBid512 (s : State) (price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let cursor := accDataWord 1 113
    let valid := accDataRbTreeValid 1 114 115 116 117 8 512 1
      (lowUInt32 (accDataWord 1 110)) (accDataWord 1 112)
      (lowUInt32 cursor) (highUInt32 cursor)
    if valid = 1 then
      accDataRbTreeOrderFind 1 110 114 115 116 117 8 512 1 price sequence
    else
      0
  else
    0

/-- Return the one-based ask slot for an exact Phoenix FIFO key in the 512-node profile. -/
@[pf_entry]
def findAsk512 (s : State) (price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let cursor := accDataWord 1 4213
    let valid := accDataRbTreeValid 1 4214 4215 4216 4217 8 512 0
      (lowUInt32 (accDataWord 1 4210)) (accDataWord 1 4212)
      (lowUInt32 cursor) (highUInt32 cursor)
    if valid = 1 then
      accDataRbTreeOrderFind 1 4210 4214 4215 4216 4217 8 512 0 price sequence
    else
      0
  else
    0

/-- Return the first bid when `hasCursor=0`, or the strict successor of the supplied FIFO key.
Only the key is retained between calls; the one-based slot result is for immediate field reads. -/
@[pf_entry]
def cursorBid512 (s : State) (hasCursor price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let cursor := accDataWord 1 113
    let valid := accDataRbTreeValid 1 114 115 116 117 8 512 1
      (lowUInt32 (accDataWord 1 110)) (accDataWord 1 112)
      (lowUInt32 cursor) (highUInt32 cursor)
    if valid = 1 then
      accDataRbTreeOrderCursor 1 110 114 115 116 117 8 512 1
        hasCursor price sequence
    else
      0
  else
    0

/-- Return the first ask when `hasCursor=0`, or the strict successor of the supplied FIFO key. -/
@[pf_entry]
def cursorAsk512 (s : State) (hasCursor price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let cursor := accDataWord 1 4213
    let valid := accDataRbTreeValid 1 4214 4215 4216 4217 8 512 0
      (lowUInt32 (accDataWord 1 4210)) (accDataWord 1 4212)
      (lowUInt32 cursor) (highUInt32 cursor)
    if valid = 1 then
      accDataRbTreeOrderCursor 1 4210 4214 4215 4216 4217 8 512 0
        hasCursor price sequence
    else
      0
  else
    0

/--
Write the links and parent/color words of one slot in the smallest official trader allocator.
`slot` is zero-based relative to the first node. The target effect requires account 1 to be writable
and owned by the executing program, then bounds both stores to the static 128 × 18-word shape.
-/
@[pf_entry]
def writeTraderTopology128 (_s : State) (slot links parentColor : UInt64) : UInt64 :=
  let _ := accDataWordSetAt 1 8314 18 128 slot links
  let _ := accDataWordSetAt 1 8315 18 128 slot parentColor
  parentColor

/--
Perform Sokoban's exact first insertion into a freshly initialized 128-seat trader allocator.
The account must have the smallest Phoenix body shape and canonical empty trader header. The
instruction initializes the complete 144-byte node (including zeroed TraderState/padding), then
publishes size and root. No detached allocated node can survive a successful instruction.
-/
@[pf_entry]
def registerFirstTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8310 = 0 && accDataWord 1 8311 = 0 &&
      accDataWord 1 8312 = 0 && accDataWord 1 8313 = 0x0000000100000001 then
    -- NodeAllocator.add_node bump path: advance bump/free boundary before initializing slot 1.
    let _ := accDataWordSetAt 1 8313 1 1 0 0x0000000200000002
    let _ := accDataWordSetAt 1 8314 18 128 0 0
    let _ := accDataWordSetAt 1 8315 18 128 0 0
    let _ := accDataWordSetAt 1 8316 18 128 0 key0
    let _ := accDataWordSetAt 1 8317 18 128 0 key1
    let _ := accDataWordSetAt 1 8318 18 128 0 key2
    let _ := accDataWordSetAt 1 8319 18 128 0 key3
    -- TraderState has four u64 balances followed by eight reserved u64 words.
    let _ := accDataWordSetAt 1 8320 18 128 0 0
    let _ := accDataWordSetAt 1 8321 18 128 0 0
    let _ := accDataWordSetAt 1 8322 18 128 0 0
    let _ := accDataWordSetAt 1 8323 18 128 0 0
    let _ := accDataWordSetAt 1 8324 18 128 0 0
    let _ := accDataWordSetAt 1 8325 18 128 0 0
    let _ := accDataWordSetAt 1 8326 18 128 0 0
    let _ := accDataWordSetAt 1 8327 18 128 0 0
    let _ := accDataWordSetAt 1 8328 18 128 0 0
    let _ := accDataWordSetAt 1 8329 18 128 0 0
    let _ := accDataWordSetAt 1 8330 18 128 0 0
    let _ := accDataWordSetAt 1 8331 18 128 0 0
    let _ := accDataWordSetAt 1 8312 1 1 0 1
    let _ := accDataWordSetAt 1 8310 1 1 0 1
    .ok ({ s with dummy := 0 }, 1)
  else
    .error .overflow

/--
Perform the exact second distinct-key insertion into the canonical one-root 128-seat trader tree.
Sokoban's bump allocator returns one-based address 2, the new node is red with parent 1, and the
existing black root receives address 2 as either its left or right child according to raw Pubkey
byte order. A second insertion never rotates because its parent is the black root.
-/
@[pf_entry]
def registerSecondTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  let rootKey0 := accDataWord 1 8316
  let rootKey1 := accDataWord 1 8317
  let rootKey2 := accDataWord 1 8318
  let rootKey3 := accDataWord 1 8319
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8310 = 1 && accDataWord 1 8311 = 0 &&
      accDataWord 1 8312 = 1 && accDataWord 1 8313 = 0x0000000200000002 &&
      accDataWord 1 8314 = 0 && accDataWord 1 8315 = 0 &&
      !key4Equal key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3 then
    let rootLinks :=
      if key4Before key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3 then
        2
      else
        0x0000000200000000
    -- NodeAllocator.add_node bump path advances address 2 to the next unused address 3.
    let _ := accDataWordSetAt 1 8313 1 1 0 0x0000000300000003
    let _ := accDataWordSetAt 1 8314 18 128 1 0
    let _ := accDataWordSetAt 1 8315 18 128 1 0x0000000100000001
    let _ := accDataWordSetAt 1 8316 18 128 1 key0
    let _ := accDataWordSetAt 1 8317 18 128 1 key1
    let _ := accDataWordSetAt 1 8318 18 128 1 key2
    let _ := accDataWordSetAt 1 8319 18 128 1 key3
    let _ := accDataWordSetAt 1 8320 18 128 1 0
    let _ := accDataWordSetAt 1 8321 18 128 1 0
    let _ := accDataWordSetAt 1 8322 18 128 1 0
    let _ := accDataWordSetAt 1 8323 18 128 1 0
    let _ := accDataWordSetAt 1 8324 18 128 1 0
    let _ := accDataWordSetAt 1 8325 18 128 1 0
    let _ := accDataWordSetAt 1 8326 18 128 1 0
    let _ := accDataWordSetAt 1 8327 18 128 1 0
    let _ := accDataWordSetAt 1 8328 18 128 1 0
    let _ := accDataWordSetAt 1 8329 18 128 1 0
    let _ := accDataWordSetAt 1 8330 18 128 1 0
    let _ := accDataWordSetAt 1 8331 18 128 1 0
    let _ := accDataWordSetAt 1 8314 18 128 0 rootLinks
    let _ := accDataWordSetAt 1 8312 1 1 0 2
    .ok ({ s with dummy := 0 }, 2)
  else
    .error .overflow

/--
Perform the exact third distinct-key insertion from a canonical two-node trader tree. Address 3
is bump-allocated and all six key placements are handled: two direct children of the black root,
plus Sokoban's LL/LR/RR/RL recolor-and-rotation outcomes. The final topology is published only as
fixed account slot indexes; no heap tree, node copy, or persistent pointer is constructed.
-/
@[pf_entry]
def registerThirdTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  let rootLinks := accDataWord 1 8314
  let rootKey0 := accDataWord 1 8316
  let rootKey1 := accDataWord 1 8317
  let rootKey2 := accDataWord 1 8318
  let rootKey3 := accDataWord 1 8319
  let childKey0 := accDataWord 1 8334
  let childKey1 := accDataWord 1 8335
  let childKey2 := accDataWord 1 8336
  let childKey3 := accDataWord 1 8337
  let childIsLeft := rootLinks = 2
  let existingOrderValid :=
    if childIsLeft then
      key4Before childKey0 childKey1 childKey2 childKey3
        rootKey0 rootKey1 rootKey2 rootKey3
    else
      key4Before rootKey0 rootKey1 rootKey2 rootKey3
        childKey0 childKey1 childKey2 childKey3
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8310 = 1 && accDataWord 1 8311 = 0 &&
      accDataWord 1 8312 = 2 && accDataWord 1 8313 = 0x0000000300000003 &&
      (childIsLeft || rootLinks = 0x0000000200000000) &&
      accDataWord 1 8315 = 0 && accDataWord 1 8332 = 0 &&
      accDataWord 1 8333 = 0x0000000100000001 && existingOrderValid &&
      !key4Equal key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3 &&
      !key4Equal key0 key1 key2 key3 childKey0 childKey1 childKey2 childKey3 then
    let newBeforeRoot :=
      key4Before key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3
    let newBeforeChild :=
      key4Before key0 key1 key2 key3 childKey0 childKey1 childKey2 childKey3
    let caseTag : UInt64 :=
      if childIsLeft then
        if newBeforeRoot then if newBeforeChild then 1 else 2 else 3
      else
        if newBeforeRoot then 6 else if newBeforeChild then 5 else 4
    let _ := accDataWordSetAt 1 8313 1 1 0 0x0000000400000004
    let _ := accDataWordSetAt 1 8314 18 128 2 (thirdNode3Links caseTag)
    let _ := accDataWordSetAt 1 8315 18 128 2 (thirdNode3ParentColor caseTag)
    let _ := accDataWordSetAt 1 8316 18 128 2 key0
    let _ := accDataWordSetAt 1 8317 18 128 2 key1
    let _ := accDataWordSetAt 1 8318 18 128 2 key2
    let _ := accDataWordSetAt 1 8319 18 128 2 key3
    let _ := accDataWordSetAt 1 8320 18 128 2 0
    let _ := accDataWordSetAt 1 8321 18 128 2 0
    let _ := accDataWordSetAt 1 8322 18 128 2 0
    let _ := accDataWordSetAt 1 8323 18 128 2 0
    let _ := accDataWordSetAt 1 8324 18 128 2 0
    let _ := accDataWordSetAt 1 8325 18 128 2 0
    let _ := accDataWordSetAt 1 8326 18 128 2 0
    let _ := accDataWordSetAt 1 8327 18 128 2 0
    let _ := accDataWordSetAt 1 8328 18 128 2 0
    let _ := accDataWordSetAt 1 8329 18 128 2 0
    let _ := accDataWordSetAt 1 8330 18 128 2 0
    let _ := accDataWordSetAt 1 8331 18 128 2 0
    let _ := accDataWordSetAt 1 8314 18 128 0 (thirdNode1Links caseTag)
    let _ := accDataWordSetAt 1 8315 18 128 0 (thirdNode1ParentColor caseTag)
    let _ := accDataWordSetAt 1 8314 18 128 1 (thirdNode2Links caseTag)
    let _ := accDataWordSetAt 1 8315 18 128 1 (thirdNode2ParentColor caseTag)
    let _ := accDataWordSetAt 1 8312 1 1 0 3
    let _ := accDataWordSetAt 1 8310 1 1 0 (thirdRoot caseTag)
    .ok ({ s with dummy := 0 }, 3)
  else
    .error .overflow

/--
Insert a fourth distinct key into any canonical three-node 128-seat trader tree. A valid
three-node red-black tree is a black root with two red leaf children. Sokoban therefore takes the
red-uncle path for every fourth-key position: attach address 4 below the selected child, recolor
both existing children black, and keep the root and all account-resident addresses unchanged.
-/
@[pf_entry]
def registerFourthTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  let root := lowUInt32 (accDataWord 1 8310)
  let rootSlot := boundedNodeSlot 128 root
  let rootLinks := accDataWordAt 1 8314 18 128 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 128 left
  let rightSlot := boundedNodeSlot 128 right
  let rootKey0 := accDataWordAt 1 8316 18 128 rootSlot
  let rootKey1 := accDataWordAt 1 8317 18 128 rootSlot
  let rootKey2 := accDataWordAt 1 8318 18 128 rootSlot
  let rootKey3 := accDataWordAt 1 8319 18 128 rootSlot
  let leftKey0 := accDataWordAt 1 8316 18 128 leftSlot
  let leftKey1 := accDataWordAt 1 8317 18 128 leftSlot
  let leftKey2 := accDataWordAt 1 8318 18 128 leftSlot
  let leftKey3 := accDataWordAt 1 8319 18 128 leftSlot
  let rightKey0 := accDataWordAt 1 8316 18 128 rightSlot
  let rightKey1 := accDataWordAt 1 8317 18 128 rightSlot
  let rightKey2 := accDataWordAt 1 8318 18 128 rightSlot
  let rightKey3 := accDataWordAt 1 8319 18 128 rightSlot
  let treeValid := accDataRbTreeKey4Valid 1 8314 8315 8316 18 128 root 3 4 4
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8311 = 0 && accDataWord 1 8312 = 3 &&
      accDataWord 1 8313 = 0x0000000400000004 && treeValid = 1 &&
      left ≠ 0 && right ≠ 0 &&
      !key4Equal key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3 &&
      !key4Equal key0 key1 key2 key3 leftKey0 leftKey1 leftKey2 leftKey3 &&
      !key4Equal key0 key1 key2 key3 rightKey0 rightKey1 rightKey2 rightKey3 then
    let newBeforeRoot :=
      key4Before key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3
    let parent := if newBeforeRoot then left else right
    let parentSlot := boundedNodeSlot 128 parent
    let newBeforeParent :=
      if newBeforeRoot then
        key4Before key0 key1 key2 key3 leftKey0 leftKey1 leftKey2 leftKey3
      else
        key4Before key0 key1 key2 key3 rightKey0 rightKey1 rightKey2 rightKey3
    let parentLinks := if newBeforeParent then 4 else 0x0000000400000000
    let _ := accDataWordSetAt 1 8313 1 1 0 0x0000000500000005
    let _ := accDataWordSetAt 1 8314 18 128 3 0
    let _ := accDataWordSetAt 1 8315 18 128 3 (parent ||| 0x0000000100000000)
    let _ := accDataWordSetAt 1 8316 18 128 3 key0
    let _ := accDataWordSetAt 1 8317 18 128 3 key1
    let _ := accDataWordSetAt 1 8318 18 128 3 key2
    let _ := accDataWordSetAt 1 8319 18 128 3 key3
    let _ := accDataWordSetAt 1 8320 18 128 3 0
    let _ := accDataWordSetAt 1 8321 18 128 3 0
    let _ := accDataWordSetAt 1 8322 18 128 3 0
    let _ := accDataWordSetAt 1 8323 18 128 3 0
    let _ := accDataWordSetAt 1 8324 18 128 3 0
    let _ := accDataWordSetAt 1 8325 18 128 3 0
    let _ := accDataWordSetAt 1 8326 18 128 3 0
    let _ := accDataWordSetAt 1 8327 18 128 3 0
    let _ := accDataWordSetAt 1 8328 18 128 3 0
    let _ := accDataWordSetAt 1 8329 18 128 3 0
    let _ := accDataWordSetAt 1 8330 18 128 3 0
    let _ := accDataWordSetAt 1 8331 18 128 3 0
    let _ := accDataWordSetAt 1 8314 18 128 parentSlot parentLinks
    let _ := accDataWordSetAt 1 8315 18 128 leftSlot root
    let _ := accDataWordSetAt 1 8315 18 128 rightSlot root
    let _ := accDataWordSetAt 1 8312 1 1 0 4
    .ok ({ s with dummy := 0 }, 4)
  else
    .error .overflow

/--
Insert a fifth distinct key into a canonical four-node 128-seat trader tree. Address 5 is allocated
from the account-resident bump cursor. If its parent is black, only that parent's missing link is
filled. If its parent is the unique red address-4 leaf, the black-uncle LL/LR/RL/RR path rotates
the local subtree below the unchanged black root. All persisted references remain one-based slot
indexes; no heap tree, map, node copy, or persistent pointer is constructed.
-/
@[pf_entry]
def registerFifthTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  let root := lowUInt32 (accDataWord 1 8310)
  let rootSlot := boundedNodeSlot 128 root
  let rootLinks := accDataWordAt 1 8314 18 128 rootSlot
  let left := lowUInt32 rootLinks
  let right := highUInt32 rootLinks
  let leftSlot := boundedNodeSlot 128 left
  let rightSlot := boundedNodeSlot 128 right
  let leftLinks := accDataWordAt 1 8314 18 128 leftSlot
  let rightLinks := accDataWordAt 1 8314 18 128 rightSlot
  let node4Links := accDataWordAt 1 8314 18 128 3
  let node4ParentColor := accDataWordAt 1 8315 18 128 3
  let redGrand := lowUInt32 node4ParentColor
  let grandLinks := if redGrand = left then leftLinks else rightLinks
  let rootKey0 := accDataWordAt 1 8316 18 128 rootSlot
  let rootKey1 := accDataWordAt 1 8317 18 128 rootSlot
  let rootKey2 := accDataWordAt 1 8318 18 128 rootSlot
  let rootKey3 := accDataWordAt 1 8319 18 128 rootSlot
  let leftKey0 := accDataWordAt 1 8316 18 128 leftSlot
  let leftKey1 := accDataWordAt 1 8317 18 128 leftSlot
  let leftKey2 := accDataWordAt 1 8318 18 128 leftSlot
  let leftKey3 := accDataWordAt 1 8319 18 128 leftSlot
  let rightKey0 := accDataWordAt 1 8316 18 128 rightSlot
  let rightKey1 := accDataWordAt 1 8317 18 128 rightSlot
  let rightKey2 := accDataWordAt 1 8318 18 128 rightSlot
  let rightKey3 := accDataWordAt 1 8319 18 128 rightSlot
  let node4Key0 := accDataWordAt 1 8316 18 128 3
  let node4Key1 := accDataWordAt 1 8317 18 128 3
  let node4Key2 := accDataWordAt 1 8318 18 128 3
  let node4Key3 := accDataWordAt 1 8319 18 128 3
  let newBeforeRoot :=
    key4Before key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3
  let selected := if newBeforeRoot then left else right
  let selectedLinks := if newBeforeRoot then leftLinks else rightLinks
  let selectedKey0 := if newBeforeRoot then leftKey0 else rightKey0
  let selectedKey1 := if newBeforeRoot then leftKey1 else rightKey1
  let selectedKey2 := if newBeforeRoot then leftKey2 else rightKey2
  let selectedKey3 := if newBeforeRoot then leftKey3 else rightKey3
  let newBeforeSelected :=
    key4Before key0 key1 key2 key3
      selectedKey0 selectedKey1 selectedKey2 selectedKey3
  let selectedChild :=
    if newBeforeSelected then lowUInt32 selectedLinks else highUInt32 selectedLinks
  let parent := if selectedChild = 0 then selected else selectedChild
  let fixNeeded := parent = 4
  let redIsLeft := lowUInt32 grandLinks = 4
  let newBeforeNode4 :=
    key4Before key0 key1 key2 key3 node4Key0 node4Key1 node4Key2 node4Key3
  let aligned := if redIsLeft then newBeforeNode4 else !newBeforeNode4
  let promoted := if aligned then 4 else 5
  let noFixParentLinks :=
    if newBeforeSelected then
      packUInt32 5 (highUInt32 selectedLinks)
    else
      packUInt32 (lowUInt32 selectedLinks) 5
  let rootLinksAfterFix :=
    if redGrand = left then packUInt32 promoted right else packUInt32 left promoted
  let node4LinksAfterFix :=
    if aligned then
      if redIsLeft then packUInt32 5 redGrand else packUInt32 redGrand 5
    else
      0
  let node4ParentColorAfterFix :=
    if aligned then packUInt32 root 0 else packUInt32 5 1
  let node5LinksAfterFix :=
    if aligned then
      0
    else if redIsLeft then
      packUInt32 4 redGrand
    else
      packUInt32 redGrand 4
  let node5ParentColorAfterFix :=
    if aligned then packUInt32 4 1 else packUInt32 root 0
  let finalRootLinks := if fixNeeded then rootLinksAfterFix else rootLinks
  let finalLeftLinks :=
    if fixNeeded then
      if redGrand = left then 0 else leftLinks
    else if parent = left then
      noFixParentLinks
    else
      leftLinks
  let finalLeftParentColor :=
    if fixNeeded && redGrand = left then packUInt32 promoted 1 else packUInt32 root 0
  let finalRightLinks :=
    if fixNeeded then
      if redGrand = right then 0 else rightLinks
    else if parent = right then
      noFixParentLinks
    else
      rightLinks
  let finalRightParentColor :=
    if fixNeeded && redGrand = right then packUInt32 promoted 1 else packUInt32 root 0
  let finalNode4Links := if fixNeeded then node4LinksAfterFix else node4Links
  let finalNode4ParentColor :=
    if fixNeeded then node4ParentColorAfterFix else node4ParentColor
  let finalNode5Links := if fixNeeded then node5LinksAfterFix else 0
  let finalNode5ParentColor :=
    if fixNeeded then node5ParentColorAfterFix else packUInt32 parent 1
  let treeValid := accDataRbTreeKey4Valid 1 8314 8315 8316 18 128 root 4 5 5
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8311 = 0 && accDataWord 1 8312 = 4 &&
      accDataWord 1 8313 = 0x0000000500000005 && treeValid = 1 &&
      left ≠ 0 && right ≠ 0 && node4Links = 0 &&
      (redGrand = left || redGrand = right) &&
      node4ParentColor = packUInt32 redGrand 1 &&
      (lowUInt32 grandLinks = 4 || highUInt32 grandLinks = 4) &&
      (selectedChild = 0 || selectedChild = 4) &&
      !key4Equal key0 key1 key2 key3 rootKey0 rootKey1 rootKey2 rootKey3 &&
      !key4Equal key0 key1 key2 key3 leftKey0 leftKey1 leftKey2 leftKey3 &&
      !key4Equal key0 key1 key2 key3 rightKey0 rightKey1 rightKey2 rightKey3 &&
      !key4Equal key0 key1 key2 key3 node4Key0 node4Key1 node4Key2 node4Key3 then
    let _ := accDataWordSetAt 1 8313 1 1 0 0x0000000600000006
    let _ := accDataWordSetAt 1 8314 18 128 4 finalNode5Links
    let _ := accDataWordSetAt 1 8315 18 128 4 finalNode5ParentColor
    let _ := accDataWordSetAt 1 8316 18 128 4 key0
    let _ := accDataWordSetAt 1 8317 18 128 4 key1
    let _ := accDataWordSetAt 1 8318 18 128 4 key2
    let _ := accDataWordSetAt 1 8319 18 128 4 key3
    let _ := accDataWordSetAt 1 8320 18 128 4 0
    let _ := accDataWordSetAt 1 8321 18 128 4 0
    let _ := accDataWordSetAt 1 8322 18 128 4 0
    let _ := accDataWordSetAt 1 8323 18 128 4 0
    let _ := accDataWordSetAt 1 8324 18 128 4 0
    let _ := accDataWordSetAt 1 8325 18 128 4 0
    let _ := accDataWordSetAt 1 8326 18 128 4 0
    let _ := accDataWordSetAt 1 8327 18 128 4 0
    let _ := accDataWordSetAt 1 8328 18 128 4 0
    let _ := accDataWordSetAt 1 8329 18 128 4 0
    let _ := accDataWordSetAt 1 8330 18 128 4 0
    let _ := accDataWordSetAt 1 8331 18 128 4 0
    let _ := accDataWordSetAt 1 8314 18 128 rootSlot finalRootLinks
    let _ := accDataWordSetAt 1 8314 18 128 leftSlot finalLeftLinks
    let _ := accDataWordSetAt 1 8315 18 128 leftSlot finalLeftParentColor
    let _ := accDataWordSetAt 1 8314 18 128 rightSlot finalRightLinks
    let _ := accDataWordSetAt 1 8315 18 128 rightSlot finalRightParentColor
    let _ := accDataWordSetAt 1 8314 18 128 3 finalNode4Links
    let _ := accDataWordSetAt 1 8315 18 128 3 finalNode4ParentColor
    let _ := accDataWordSetAt 1 8312 1 1 0 5
    .ok ({ s with dummy := 0 }, 5)
  else
    .error .overflow

/--
Insert any distinct trader key into the smallest official Phoenix allocator through the generic
bounded account-resident red-black insertion effect. Static geometry fixes the four-word Sokoban
header and 128 complete 18-word slots. The effect validates the whole current tree/free partition,
then applies general search, bump/free-list allocation, and insertion fixup in place. It zeroes the
entire allocated slot before publishing the new key, so TraderState starts canonical without a
heap node, Map, persistent pointer, or count-specific topology case.
-/
@[pf_entry]
def registerTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8311 = 0 then
    let _ := accDataRbTreeKey4Insert 1 8310 8314 8315 8316 18 128
      key0 key1 key2 key3
    let size := accDataWord 1 8312
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/--
Apply Phoenix's fixed-capacity trader get-or-register deposit primitive to the smallest official
market. Existing traders receive checked additions to quote/base free lots; absent traders receive
a canonical zeroed 96-byte `TraderState` whose free balances are initialized from the deposit.
Both paths mutate the account-resident 128-seat Sokoban tree directly, with no heap Map, copied
tree, persistent pointer, or runtime capacity.
-/
@[pf_entry]
def depositTrader128 (s : State) (key0 key1 key2 key3 quoteLots baseLots : UInt64) :
    Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8311 = 0 then
    let _ := accDataRbTreeTraderDeposit 1 8310 8314 8315 8316 18 128
      key0 key1 key2 key3 quoteLots baseLots
    let size := accDataWord 1 8312
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/--
Remove a registered trader key from the smallest official Phoenix allocator through the generic
bounded account-resident red-black deletion effect. The effect validates the complete tree/free
partition before mutation, applies Sokoban 0.3.0 predecessor transplant and delete-fixup, and
returns the removed one-based slot to the in-account free list. It does not allocate or persist a
heap pointer, Map, detached node, or copied tree.
-/
@[pf_entry]
def removeTrader128 (s : State) (key0 key1 key2 key3 : UInt64) :
    Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 8311 = 0 then
    let _ := accDataRbTreeKey4Remove 1 8310 8314 8315 8316 18 128
      key0 key1 key2 key3
    let size := accDataWord 1 8312
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/--
Insert one encoded Phoenix bid into the smallest official 512-node book. The key and complete
`FIFORestingOrder` value are written directly into the fixed 64-byte Sokoban slot; incoming bid
sequence must have its high bit set. This is the account-resident order-tree mutation primitive,
not yet the full Phoenix placement/matching instruction.
-/
@[pf_entry]
def insertBid512 (s : State) (price sequence traderIndex numBaseLots lastValidSlot
    lastValidUnixTimestamp : UInt64) : Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 111 = 0 then
    let _ := accDataRbTreeOrderInsert 1 110 114 115 116 117 8 512 1
      price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp
    let size := accDataWord 1 112
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/-- The ask-side twin of `insertBid512`; encoded ask sequence must have high bit zero. -/
@[pf_entry]
def insertAsk512 (s : State) (price sequence traderIndex numBaseLots lastValidSlot
    lastValidUnixTimestamp : UInt64) : Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 4211 = 0 then
    let _ := accDataRbTreeOrderInsert 1 4210 4214 4215 4216 4217 8 512 0
      price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp
    let size := accDataWord 1 4212
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/--
Remove one encoded Phoenix bid from the smallest official 512-node book. The complete tree and
free partition plus the bid sequence high-bit tag are validated before the first account store;
the removed one-based slot is returned to the fixed in-account free list.
-/
@[pf_entry]
def removeBid512 (s : State) (price sequence : UInt64) : Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 111 = 0 then
    let _ := accDataRbTreeOrderRemove 1 110 114 115 116 117 8 512 1 price sequence
    let size := accDataWord 1 112
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/-- The ask-side twin of `removeBid512`; encoded ask sequence must have high bit zero. -/
@[pf_entry]
def removeAsk512 (s : State) (price sequence : UInt64) : Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 4211 = 0 then
    let _ := accDataRbTreeOrderRemove 1 4210 4214 4215 4216 4217 8 512 0 price sequence
    let size := accDataWord 1 4212
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/-!
These two reducers are account-index-parametric only at extraction time. Generated verifier methods
instantiate `(market, trader) = (1, 0)`; the official raw adapter instantiates `(2, 3)`. Every
resulting `AccountStorage` descriptor still has literal account/base/stride/capacity geometry.
-/

def reduceAskFreeFunds512At (marketAccount traderAccount traderKey0 price sequence requested :
    UInt64) : Except Error UInt64 :=
  if profileAccountBytesAt marketAccount = 84944 &&
      allocatorHeadersValidAt marketAccount = 1 then
    let traderCursor := accDataWord marketAccount 8313
    let askCursor := accDataWord marketAccount 4213
    let traderValid := accDataRbTreeKey4Valid marketAccount 8314 8315 8316 18 128
      (lowUInt32 (accDataWord marketAccount 8310)) (accDataWord marketAccount 8312)
      (lowUInt32 traderCursor) (highUInt32 traderCursor)
    let askValid := accDataRbTreeValid marketAccount 4214 4215 4216 4217 8 512 0
      (lowUInt32 (accDataWord marketAccount 4210)) (accDataWord marketAccount 4212)
      (lowUInt32 askCursor) (highUInt32 askCursor)
    if traderValid = 1 && askValid = 1 then
      let traderIndex := accDataRbTreeKey4Find marketAccount 8310 8314 8315 8316 18 128
        traderKey0 (accKeyWord traderAccount 1) (accKeyWord traderAccount 2)
        (accKeyWord traderAccount 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex := accDataRbTreeOrderFind marketAccount 4210 4214 4215 4216 4217
          8 512 0 price sequence
        if orderIndex = 0 then
          .ok 0
        else
          let orderTrader := accDataWordAtOneBased marketAccount 4218 8 512 orderIndex
          let resting := accDataWordAtOneBased marketAccount 4219 8 512 orderIndex
          if orderTrader ≠ traderIndex then
            .error .overflow
          else
            let removed := if requested ≤ resting then requested else resting
            let locked := accDataWordAtOneBased marketAccount 8322 18 128 traderIndex
            let free := accDataWordAtOneBased marketAccount 8323 18 128 traderIndex
            if removed ≤ locked && free ≤ u64Max - removed then
              let remaining := resting - removed
              let nextLocked := locked - removed
              let nextFree := free + removed
              if remaining = 0 then
                let _ := accDataRbTreeOrderRemove marketAccount 4210 4214 4215 4216 4217
                  8 512 0 price sequence
                let _ := accDataWordSetAtOneBased marketAccount 8322 18 128
                  traderIndex nextLocked
                let _ := accDataWordSetAtOneBased marketAccount 8323 18 128
                  traderIndex nextFree
                .ok removed
              else
                let _ := accDataWordSetAtOneBased marketAccount 4219 8 512
                  orderIndex remaining
                let _ := accDataWordSetAtOneBased marketAccount 8322 18 128
                  traderIndex nextLocked
                let _ := accDataWordSetAtOneBased marketAccount 8323 18 128
                  traderIndex nextFree
                .ok removed
            else
              .error .overflow
    else
      .error .overflow
  else
    .error .overflow

def reduceBidFreeFunds512At (marketAccount traderAccount traderKey0 price sequence requested :
    UInt64) : Except Error UInt64 :=
  if profileAccountBytesAt marketAccount = 84944 &&
      allocatorHeadersValidAt marketAccount = 1 then
    let traderCursor := accDataWord marketAccount 8313
    let bidCursor := accDataWord marketAccount 113
    let traderValid := accDataRbTreeKey4Valid marketAccount 8314 8315 8316 18 128
      (lowUInt32 (accDataWord marketAccount 8310)) (accDataWord marketAccount 8312)
      (lowUInt32 traderCursor) (highUInt32 traderCursor)
    let bidValid := accDataRbTreeValid marketAccount 114 115 116 117 8 512 1
      (lowUInt32 (accDataWord marketAccount 110)) (accDataWord marketAccount 112)
      (lowUInt32 bidCursor) (highUInt32 bidCursor)
    if traderValid = 1 && bidValid = 1 then
      let traderIndex := accDataRbTreeKey4Find marketAccount 8310 8314 8315 8316 18 128
        traderKey0 (accKeyWord traderAccount 1) (accKeyWord traderAccount 2)
        (accKeyWord traderAccount 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex := accDataRbTreeOrderFind marketAccount 110 114 115 116 117
          8 512 1 price sequence
        if orderIndex = 0 then
          .ok 0
        else
          let orderTrader := accDataWordAtOneBased marketAccount 118 8 512 orderIndex
          let resting := accDataWordAtOneBased marketAccount 119 8 512 orderIndex
          if orderTrader ≠ traderIndex then
            .error .overflow
          else
            let removed := if requested ≤ resting then requested else resting
            let baseLotsPerBaseUnit := accDataWord marketAccount 104
            let tickSize := accDataWord marketAccount 105
            if baseLotsPerBaseUnit = 0 then
              .error .overflow
            else if price = 0 || tickSize ≤ u64Max / price then
              let quotePerBase := price * tickSize
              if removed = 0 || quotePerBase ≤ u64Max / removed then
                let unlocked := (quotePerBase * removed) / baseLotsPerBaseUnit
                let locked := accDataWordAtOneBased marketAccount 8320 18 128 traderIndex
                let free := accDataWordAtOneBased marketAccount 8321 18 128 traderIndex
                if unlocked ≤ locked && free ≤ u64Max - unlocked then
                  let remaining := resting - removed
                  let nextLocked := locked - unlocked
                  let nextFree := free + unlocked
                  if remaining = 0 then
                    let _ := accDataRbTreeOrderRemove marketAccount 110 114 115 116 117
                      8 512 1 price sequence
                    let _ := accDataWordSetAtOneBased marketAccount 8320 18 128
                      traderIndex nextLocked
                    let _ := accDataWordSetAtOneBased marketAccount 8321 18 128
                      traderIndex nextFree
                    .ok removed
                  else
                    let _ := accDataWordSetAtOneBased marketAccount 119 8 512
                      orderIndex remaining
                    let _ := accDataWordSetAtOneBased marketAccount 8320 18 128
                      traderIndex nextLocked
                    let _ := accDataWordSetAtOneBased marketAccount 8321 18 128
                      traderIndex nextFree
                    .ok removed
                else
                  .error .overflow
              else
                .error .overflow
            else
              .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Select the fixed-capacity bid/ask reducer before protocol-adapter sequencing. Keeping side
dispatch inside this reusable account-storage component gives generated and raw adapters the same
bounded mutation contract. -/
def reduceFreeFunds512At (marketAccount traderAccount traderKey0 side price sequence requested :
    UInt64) : Except Error UInt64 :=
  if side = 0 then
    reduceBidFreeFunds512At marketAccount traderAccount traderKey0 price sequence requested
  else
    reduceAskFreeFunds512At marketAccount traderAccount traderKey0 price sequence requested

/-- Compute the bid-side quote lots released by the same pinned market scalars as the reducer. -/
def quoteLotsReleased512At (marketAccount price removed : UInt64) : Except Error UInt64 :=
  let baseLotsPerBaseUnit := accDataWord marketAccount 104
  let tickSize := accDataWord marketAccount 105
  if baseLotsPerBaseUnit = 0 then
    .error .overflow
  else if price = 0 || tickSize ≤ u64Max / price then
    let quotePerBase := price * tickSize
    if removed = 0 || quotePerBase ≤ u64Max / removed then
      .ok ((quotePerBase * removed) / baseLotsPerBaseUnit)
    else
      .error .overflow
  else
    .error .overflow

/-- Claim exactly the lots just released by `reduceFreeFunds512At`. This composes literal
one-based account-storage writes and leaves any pre-existing free balance untouched. -/
def claimReleasedFunds512At (marketAccount traderIndex side released : UInt64) :
    Except Error UInt64 :=
  if side = 0 then
    let free := accDataWordAtOneBased marketAccount 8321 18 128 traderIndex
    if released ≤ free then
      let _ := accDataWordSetAtOneBased marketAccount 8321 18 128 traderIndex (free - released)
      .ok released
    else
      .error .overflow
  else
    let free := accDataWordAtOneBased marketAccount 8323 18 128 traderIndex
    if released ≤ free then
      let _ := accDataWordSetAtOneBased marketAccount 8323 18 128 traderIndex (free - released)
      .ok released
    else
      .error .overflow

/-- Open Phoenix's bounded audit batch. `traderCpiAccount` is external-relative because it is
embedded as a CPI data key; market reads remain physical indexes. The 92-byte payload below plus
the component-owned raw-entry byte is Phoenix's 93-byte audit header. -/
def beginReduceBatchAt (origin marketAccount traderCpiAccount marketSequence : UInt64) : UInt64 :=
  batchRecorderBegin 0 15 "log" 1246 93 91 32
    #[.u8le 1, .u8le origin,
      .u64le marketSequence, .u64le unixTime, .u64le clockSlot,
      .u64le (accKeyWord marketAccount 0), .u64le (accKeyWord marketAccount 1),
      .u64le (accKeyWord marketAccount 2), .u64le (accKeyWord marketAccount 3),
      .accKey traderCpiAccount, .u16le 0]
    (findPda "log")

/-- Append one canonical 35-byte Phoenix Reduce record. `orderIndex = 0` disables the append while
leaving `finishReduceBatch` responsible for the required header-only CPI. -/
def recordReduceAt (orderIndex orderSequence price removed remaining : UInt64) : UInt64 :=
  batchRecorderAppend 0 15 "log" 1246 93 91 32 orderIndex
    #[.u8le 4, .u16le 0, .u64le orderSequence, .u64le price,
      .u64le removed, .u64le remaining]

/-- Flush Phoenix's current batch, including an empty header-only batch, and close the recorder. -/
def finishReduceBatch : UInt64 :=
  batchRecorderFinish 0 15 "log" 1246 93 91 32

/-- Execute only the side-selected nonzero classic Token withdrawal. The mint seed points directly
at the authenticated fixed MarketHeader field; no mint account, heap buffer, or copied seed exists. -/
def withdrawReleasedAt (side atoms : UInt64) : UInt64 :=
  if atoms = 0 then
    0
  else if side = 0 then
    let seeds : Array PdaSeed := #[.ascii "vault", .accKey 1, .accData 1 128 32]
    tokenTransferSignedIx 7 6 4 6 atoms seeds (highUInt32 (accDataWord 2 15))
  else
    let seeds : Array PdaSeed := #[.ascii "vault", .accKey 1, .accData 1 48 32]
    tokenTransferSignedIx 7 5 3 5 atoms seeds (highUInt32 (accDataWord 2 5))

/-- Complete dominating validation required by the component-owned CancelAll mutation loop. The
three fixed allocators, trader key tree, and both FIFO trees are validated before the recorder can
emit or any account byte can change. A missing trader remains distinct: this function succeeds and
the subsequent bounded find returns the zero sentinel. -/
def cancelAllStorageValid512At (marketAccount : UInt64) : UInt64 :=
  if profileAccountBytesAt marketAccount = 84944 &&
      accDataWord marketAccount 106 ≠ 0 &&
      allocatorHeadersValidAt marketAccount = 1 then
    let traderCursor := accDataWord marketAccount 8313
    let bidCursor := accDataWord marketAccount 113
    let askCursor := accDataWord marketAccount 4213
    let traderValid := accDataRbTreeKey4Valid marketAccount 8314 8315 8316 18 128
      (lowUInt32 (accDataWord marketAccount 8310)) (accDataWord marketAccount 8312)
      (lowUInt32 traderCursor) (highUInt32 traderCursor)
    let bidValid := accDataRbTreeValid marketAccount 114 115 116 117 8 512 1
      (lowUInt32 (accDataWord marketAccount 110)) (accDataWord marketAccount 112)
      (lowUInt32 bidCursor) (highUInt32 bidCursor)
    let askValid := accDataRbTreeValid marketAccount 4214 4215 4216 4217 8 512 0
      (lowUInt32 (accDataWord marketAccount 4210)) (accDataWord marketAccount 4212)
      (lowUInt32 askCursor) (highUInt32 askCursor)
    if traderValid = 1 && bidValid = 1 && askValid = 1 then 1 else 0
  else
    0

/-- Find the official one-based trader slot after `cancelAllStorageValid512At` has dominated the
operation. Zero is the account-resident null sentinel and implements missing-trader success. -/
def cancelAllTraderIndex512At (marketAccount traderAccount : UInt64) : UInt64 :=
  accDataRbTreeKey4Find marketAccount 8310 8314 8315 8316 18 128
    (signerKey traderAccount) (accKeyWord traderAccount 1)
    (accKeyWord traderAccount 2) (accKeyWord traderAccount 3)

/-- Open the invocation-local scalar accumulator shared by both FIFO passes. -/
def beginCancelAll : UInt64 := fifoCancelBegin

/-- Cancel owned bids in Phoenix logical FIFO order. Static account geometry, collateral math, and
audit recording are owned by the bounded component rather than the generic SVM operation set. -/
def cancelAllBids512At (marketAccount traderIndex : UInt64) : UInt64 :=
  fifoCancelSide marketAccount 110 114 115 116 117 118 119 8320 8321
    8 512 18 128 1 104 105 0 15 "log" 1246 93 91 32 traderIndex

/-- Cancel owned asks after the bid pass, preserving one invocation-global event index. -/
def cancelAllAsks512At (marketAccount traderIndex : UInt64) : UInt64 :=
  fifoCancelSide marketAccount 4210 4214 4215 4216 4217 4218 4219 8322 8323
    8 512 18 128 0 104 105 0 15 "log" 1246 93 91 32 traderIndex

/-- Close the FIFO accumulator after all aggregate results have been consumed. -/
def finishCancelAll : UInt64 := fifoCancelFinish

/-- Shared official Token-context gate for tags 4 and 6. It authenticates the fixed raw account
shape, market status, classic SPL Token program, trader destinations, vault keys, mints, and vault
authorities before either storage mutation or CPI can occur. -/
def cancelWithdrawContextValid : UInt64 :=
  if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      isWritable 4 = 0 || isWritable 5 = 0 || isWritable 6 = 0 || isWritable 7 = 0 ||
      isWritable 8 ≠ 0 || checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
    0
  else if profileAccountBytesAt 2 ≠ 84944 then
    0
  else if reduceStatusValidAt 2 = 0 then
    0
  else if splTokenProgramValidAt 8 = 0 then
    0
  else if accDataLen 4 ≠ 165 || !key4Equal
      (accOwnerWord 4 0) (accOwnerWord 4 1) (accOwnerWord 4 2) (accOwnerWord 4 3)
      (accKeyWord 8 0) (accKeyWord 8 1) (accKeyWord 8 2) (accKeyWord 8 3) then
    0
  else if !key4Equal
      (accDataWord 4 0) (accDataWord 4 1) (accDataWord 4 2) (accDataWord 4 3)
      (accDataWord 2 6) (accDataWord 2 7) (accDataWord 2 8) (accDataWord 2 9) then
    0
  else if !key4Equal
      (accDataWord 4 4) (accDataWord 4 5) (accDataWord 4 6) (accDataWord 4 7)
      (accKeyWord 3 0) (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3) then
    0
  else if accDataLen 5 ≠ 165 || !key4Equal
      (accOwnerWord 5 0) (accOwnerWord 5 1) (accOwnerWord 5 2) (accOwnerWord 5 3)
      (accKeyWord 8 0) (accKeyWord 8 1) (accKeyWord 8 2) (accKeyWord 8 3) then
    0
  else if !key4Equal
      (accDataWord 5 0) (accDataWord 5 1) (accDataWord 5 2) (accDataWord 5 3)
      (accDataWord 2 16) (accDataWord 2 17) (accDataWord 2 18) (accDataWord 2 19) then
    0
  else if !key4Equal
      (accDataWord 5 4) (accDataWord 5 5) (accDataWord 5 6) (accDataWord 5 7)
      (accKeyWord 3 0) (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3) then
    0
  else if !key4Equal
      (accKeyWord 6 0) (accKeyWord 6 1) (accKeyWord 6 2) (accKeyWord 6 3)
      (accDataWord 2 10) (accDataWord 2 11) (accDataWord 2 12) (accDataWord 2 13) then
    0
  else if accDataLen 6 ≠ 165 || !key4Equal
      (accOwnerWord 6 0) (accOwnerWord 6 1) (accOwnerWord 6 2) (accOwnerWord 6 3)
      (accKeyWord 8 0) (accKeyWord 8 1) (accKeyWord 8 2) (accKeyWord 8 3) then
    0
  else if !key4Equal
      (accDataWord 6 0) (accDataWord 6 1) (accDataWord 6 2) (accDataWord 6 3)
      (accDataWord 2 6) (accDataWord 2 7) (accDataWord 2 8) (accDataWord 2 9) then
    0
  else if !key4Equal
      (accDataWord 6 4) (accDataWord 6 5) (accDataWord 6 6) (accDataWord 6 7)
      (accKeyWord 6 0) (accKeyWord 6 1) (accKeyWord 6 2) (accKeyWord 6 3) then
    0
  else if !key4Equal
      (accKeyWord 7 0) (accKeyWord 7 1) (accKeyWord 7 2) (accKeyWord 7 3)
      (accDataWord 2 20) (accDataWord 2 21) (accDataWord 2 22) (accDataWord 2 23) then
    0
  else if accDataLen 7 ≠ 165 || !key4Equal
      (accOwnerWord 7 0) (accOwnerWord 7 1) (accOwnerWord 7 2) (accOwnerWord 7 3)
      (accKeyWord 8 0) (accKeyWord 8 1) (accKeyWord 8 2) (accKeyWord 8 3) then
    0
  else if !key4Equal
      (accDataWord 7 0) (accDataWord 7 1) (accDataWord 7 2) (accDataWord 7 3)
      (accDataWord 2 16) (accDataWord 2 17) (accDataWord 2 18) (accDataWord 2 19) then
    0
  else if !key4Equal
      (accDataWord 7 4) (accDataWord 7 5) (accDataWord 7 6) (accDataWord 7 7)
      (accKeyWord 7 0) (accKeyWord 7 1) (accKeyWord 7 2) (accKeyWord 7 3) then
    0
  else
    1

/-- Historical generated adapters retain their existing account geometry and IDL. -/
@[pf_entry]
def reduceAskFreeFunds512 (s : State) (price sequence requested : UInt64) :
    Except Error (State × UInt64) := do
  let removed ← reduceAskFreeFunds512At 1 0 (accKeyWord 0 0) price sequence requested
  .ok (s, removed)

@[pf_entry]
def reduceBidFreeFunds512 (s : State) (price sequence requested : UInt64) :
    Except Error (State × UInt64) := do
  let removed ← reduceBidFreeFunds512At 1 0 (accKeyWord 0 0) price sequence requested
  .ok (s, removed)

/--
Official Phoenix `ReduceOrderWithFreeFunds` wire for the smallest static profile:
`05 || side:u8 || price:u64 || sequence:u64 || size:u64`. Physical accounts are current program,
canonical `"log"` PDA, writable market, and readonly signer. Missing orders emit a header-only audit
batch and advance the market-header sequence; existing orders append one canonical 35-byte Reduce
event. No Token account or withdrawal CPI is involved.
-/
@[pf_entry, pf_svm_raw 5 4 0]
def reduceOrderWithFreeFunds (_s : State) (side : UInt8)
    (price sequence requested : UInt64) : Except Error (State × UInt64) := do
  if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
    .error .overflow
  else
    let side := side.toUInt64
    if side ≠ 0 && side ≠ 1 then
      .error .overflow
    else
      let orderIndex :=
        if side = 0 then
          accDataRbTreeOrderFind 2 110 114 115 116 117 8 512 1 price sequence
        else
          accDataRbTreeOrderFind 2 4210 4214 4215 4216 4217 8 512 0 price sequence
      let resting :=
        if orderIndex = 0 then 0
        else if side = 0 then accDataWordAtOneBased 2 119 8 512 orderIndex
        else accDataWordAtOneBased 2 4219 8 512 orderIndex
      let traderKey0 := signerKey 3
      let removed ← reduceFreeFunds512At 2 3 traderKey0 side price sequence requested
      let marketSequence := accDataWord 2 106
      let remaining := resting - removed
      let _ := accDataWordSetAt 2 106 1 1 0 (marketSequence + 1)
      let _ := beginReduceBatchAt 5 2 2 marketSequence
      let _ := recordReduceAt orderIndex sequence price removed remaining
      let _ := finishReduceBatch
      .ok (_s, removed)

/--
Official Phoenix `ReduceOrder` tag 4 adds five validated classic SPL Token accounts to the same
wire body. The bounded reducer releases collateral, this adapter claims exactly that delta, performs
the side-selected nonzero vault withdrawal with `["vault", market, mint, bump]`, increments audit
sequence, and emits the same Reduce record with origin 4.
-/
@[pf_entry, pf_svm_raw 4 9 0]
def reduceOrder (_s : State) (side : UInt8)
    (price sequence requested : UInt64) : Except Error (State × UInt64) := do
  if cancelWithdrawContextValid = 0 then
    .error .overflow
  else
    let side := side.toUInt64
    if side ≠ 0 && side ≠ 1 then
      .error .overflow
    else
      let traderKey0 := signerKey 3
      let traderIndex := accDataRbTreeKey4Find 2 8310 8314 8315 8316 18 128
        traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex :=
          if side = 0 then
            accDataRbTreeOrderFind 2 110 114 115 116 117 8 512 1 price sequence
          else
            accDataRbTreeOrderFind 2 4210 4214 4215 4216 4217 8 512 0 price sequence
        let resting :=
          if orderIndex = 0 then 0
          else if side = 0 then accDataWordAtOneBased 2 119 8 512 orderIndex
          else accDataWordAtOneBased 2 4219 8 512 orderIndex
        let removed := if requested ≤ resting then requested else resting
        let released ←
          if side = 0 then quoteLotsReleased512At 2 price removed else .ok removed
        let lotSize := if side = 0 then accDataWord 2 24 else accDataWord 2 14
        let releasedDivisor := if released = 0 then 1 else released
        if lotSize ≤ u64Max / releasedDivisor then
          let atoms := released * lotSize
          let actual ← reduceFreeFunds512At 2 3 traderKey0 side price sequence requested
          if actual ≠ removed then
            .error .overflow
          else
            let _ ← claimReleasedFunds512At 2 traderIndex side released
            let _ := withdrawReleasedAt side atoms
            let marketSequence := accDataWord 2 106
            let _ := accDataWordSetAt 2 106 1 1 0 (marketSequence + 1)
            let _ := beginReduceBatchAt 4 2 2 marketSequence
            let _ := recordReduceAt orderIndex sequence price actual (resting - actual)
            let _ := finishReduceBatch
            .ok (_s, actual)
        else
          .error .overflow

/--
Official Phoenix `CancelAllOrdersWithFreeFunds` tag 7 has no payload and uses the four-account
cancel-only context. Complete trader/bid/ask validation dominates two component-owned bounded
passes. Bids are canceled before asks, missing traders and empty books still advance sequence and
emit one header-only batch, and no Token CPI is possible.
-/
@[pf_entry, pf_svm_raw 7 4 0]
def cancelAllOrdersWithFreeFunds (_s : State) : Except Error (State × UInt64) := do
  if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
    .error .overflow
  else if cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := accDataWord 2 106
    let _ := accDataWordSetAt 2 106 1 1 0 (marketSequence + 1)
    let _ := beginReduceBatchAt 7 2 2 marketSequence
    let _ := beginCancelAll
    let _ := cancelAllBids512At 2 traderIndex
    let _ := cancelAllAsks512At 2 traderIndex
    let _ := finishCancelAll
    let _ := finishReduceBatch
    .ok (_s, 0)

/--
Official Phoenix `CancelAllOrders` tag 6 composes the same bounded bid/ask passes with the shared
tag-4 Token context. The component reports only lots released by this invocation; the adapter
claims exactly those deltas, preserves pre-existing free balances, and performs quote withdrawal
before base withdrawal as required by Phoenix-v1.
-/
@[pf_entry, pf_svm_raw 6 9 0]
def cancelAllOrders (_s : State) : Except Error (State × UInt64) := do
  if cancelWithdrawContextValid = 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := accDataWord 2 106
    let _ := accDataWordSetAt 2 106 1 1 0 (marketSequence + 1)
    let _ := beginReduceBatchAt 6 2 2 marketSequence
    let _ := beginCancelAll
    let _ := cancelAllBids512At 2 traderIndex
    let _ := cancelAllAsks512At 2 traderIndex
    let quoteReleased := fifoCancelQuoteReleased
    let baseReleased := fifoCancelBaseReleased
    let quoteLotSize := accDataWord 2 24
    let baseLotSize := accDataWord 2 14
    let quoteDivisor := if quoteReleased = 0 then 1 else quoteReleased
    let baseDivisor := if baseReleased = 0 then 1 else baseReleased
    if quoteLotSize ≤ u64Max / quoteDivisor && baseLotSize ≤ u64Max / baseDivisor then
      let quoteAtoms := quoteReleased * quoteLotSize
      let baseAtoms := baseReleased * baseLotSize
      let _ ←
        if traderIndex = 0 then .ok 0
        else claimReleasedFunds512At 2 traderIndex 0 quoteReleased
      let _ := withdrawReleasedAt 0 quoteAtoms
      let _ ←
        if traderIndex = 0 then .ok 0
        else claimReleasedFunds512At 2 traderIndex 1 baseReleased
      let _ := withdrawReleasedAt 1 baseAtoms
      let _ := finishCancelAll
      let _ := finishReduceBatch
      .ok (_s, 0)
    else
      .error .overflow

/-- Direct boundary probe used to prove a short account fails before reading bytes 32..39. -/
@[pf_entry]
def headerSeats (_s : State) : UInt64 :=
  accDataWord 1 4

attribute [pf_inline] accountBytesFor boundedBodyEntryCount lowUInt32 highUInt32 packUInt32
  key4Before key4Equal splTokenProgramValidAt reduceStatusValidAt
  thirdRoot thirdNode1Links thirdNode1ParentColor thirdNode2Links
  thirdNode2ParentColor thirdNode3Links thirdNode3ParentColor
  allocatorHeaderValid threeAllocatorHeadersValid nodeIndexOrNullValid boundedBidRootPrice
  boundedNodeSlot bidKeyBefore boundedBidChildValid boundedBidRootNeighborhoodValid
  bidRootNeighborhood512 bidRootNeighborhood1024 bidRootNeighborhood2048
  bidRootNeighborhood4096 profileAccountBytesAt profileAccountBytes allocatorHeadersValidAt
  allocatorHeadersValid reduceAskFreeFunds512At reduceBidFreeFunds512At reduceFreeFunds512At
  quoteLotsReleased512At claimReleasedFunds512At beginReduceBatchAt recordReduceAt
  finishReduceBatch withdrawReleasedAt cancelAllStorageValid512At cancelAllTraderIndex512At
  beginCancelAll cancelAllBids512At cancelAllAsks512At finishCancelAll
  cancelWithdrawContextValid

end Projects.PhoenixV1Profile
