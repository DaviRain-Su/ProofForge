import ProofForge
import Examples.Svm.PhoenixV1Layout

/-!
Phoenix v1 market-account profile gate.

The official program does not accept arbitrary runtime capacities. Its 24-byte `MarketSizeParams`
header selects one of twelve statically compiled `FIFOMarket<Pubkey, B, A, S>` layouts. This module
validates that dispatch boundary, fixed scalar/allocator metadata, and all three complete trees
plus allocator partitions against the pinned Sokoban 0.3.0 layout.

This is deliberately a separate verifier/profile program. Generated probes keep ProofForge state in
account 0 and the candidate market in account 1; the official raw adapter instead authenticates a
physical program prefix and mutates the market in account 2. Its fixed-shape Sokoban routines are
Official instruction coverage includes tags 4–12 plus a strict PostOnly/no-TIF/deposited-funds-only
slice of tag 3, not the complete Phoenix instruction set.
-/
namespace Examples.Svm.PhoenixV1Profile
open ProofForge.Svm.Runtime
open ProofForge.Svm
open ProofForge.Svm.Sdk
open ProofForge.Core.Value

def phoenixProgramOwner0 : UInt64 := 11497730047637682189
def phoenixProgramOwner1 : UInt64 := 2178672117088209453
def phoenixProgramOwner2 : UInt64 := 16206118848139790065
def phoenixProgramOwner3 : UInt64 := 1630085884070697098

def marketHeaderDiscriminant : UInt64 := 8167313896524341111
def seatDiscriminant : UInt64 := 2002603505298356104
def marketHeaderBytes : UInt64 := 576
def u64Max : UInt64 := 0xffffffffffffffff
def maxOrderSequence : UInt64 := 0x7fffffffffffffff

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

/-- Return `MarketHeader.market_sequence_number` at absolute account word 34. This is distinct
from the FIFO body's `order_sequence_number` at word 106. -/
@[pf_entry]
def marketSequence (s : State) : UInt64 :=
  if profileAccountBytes s = 0 then 0 else accDataWord 1 34

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
    let layout := Examples.Svm.PhoenixV1.small 1
    if layout.tradersValid = 1 then
      layout.findTrader key0 key1 key2 key3
    else
      0
  else
    0

/-- Return the one-based bid slot for an exact Phoenix FIFO key in the 512-node profile. -/
@[pf_entry]
def findBid512 (s : State) (price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let layout := Examples.Svm.PhoenixV1.small 1
    if layout.bidsValid = 1 then
      layout.findBid price sequence
    else
      0
  else
    0

/-- Return the one-based ask slot for an exact Phoenix FIFO key in the 512-node profile. -/
@[pf_entry]
def findAsk512 (s : State) (price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let layout := Examples.Svm.PhoenixV1.small 1
    if layout.asksValid = 1 then
      layout.findAsk price sequence
    else
      0
  else
    0

/-- Return the first bid when `hasCursor=0`, or the strict successor of the supplied FIFO key.
Only the key is retained between calls; the one-based slot result is for immediate field reads. -/
@[pf_entry]
def cursorBid512 (s : State) (hasCursor price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let layout := Examples.Svm.PhoenixV1.small 1
    if layout.bidsValid = 1 then
      layout.bids.cursor hasCursor price sequence
    else
      0
  else
    0

/-- Return the first ask when `hasCursor=0`, or the strict successor of the supplied FIFO key. -/
@[pf_entry]
def cursorAsk512 (s : State) (hasCursor price sequence : UInt64) : UInt64 :=
  if profileAccountBytes s = 84944 && allocatorHeadersValid s = 1 then
    let layout := Examples.Svm.PhoenixV1.small 1
    if layout.asksValid = 1 then
      layout.asks.cursor hasCursor price sequence
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
    let layout := Examples.Svm.PhoenixV1.small 1
    let _ := layout.insertBid
      price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp
    let size := layout.bidSize
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
    let layout := Examples.Svm.PhoenixV1.small 1
    let _ := layout.insertAsk
      price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp
    let size := layout.askSize
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
    let layout := Examples.Svm.PhoenixV1.small 1
    let _ := layout.removeBid price sequence
    let size := layout.bidSize
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/-- The ask-side twin of `removeBid512`; encoded ask sequence must have high bit zero. -/
@[pf_entry]
def removeAsk512 (s : State) (price sequence : UInt64) : Except Error (State × UInt64) :=
  if accDataLen 1 = 84944 && accDataWord 1 0 = marketHeaderDiscriminant &&
      accDataWord 1 2 = 512 && accDataWord 1 3 = 512 && accDataWord 1 4 = 128 &&
      accDataWord 1 4211 = 0 then
    let layout := Examples.Svm.PhoenixV1.small 1
    let _ := layout.removeAsk price sequence
    let size := layout.askSize
    .ok ({ s with dummy := 0 }, size)
  else
    .error .overflow

/-!
These two reducers receive a compile-time Phoenix layout and a runtime trader identity. Generated
verifier methods instantiate `small 1`; the official raw adapter instantiates `small 2`. Extraction
erases the layout and leaves only the reusable `AccountStorage` component calls with literal
account/base/stride/capacity geometry.
-/

def reduceAskFreeFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (marketAccount traderAccount traderKey0 price sequence requested : UInt64) :
    Except Error UInt64 :=
  if profileAccountBytesAt marketAccount = UInt64.ofNat layout.accountBytes &&
      allocatorHeadersValidAt marketAccount = 1 then
    if layout.tradersValid = 1 && layout.asksValid = 1 then
      let traderIndex := layout.findTrader
        traderKey0 (accKeyWord traderAccount 1) (accKeyWord traderAccount 2)
        (accKeyWord traderAccount 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex := layout.findAsk price sequence
        if orderIndex = 0 then
          .ok 0
        else
          let orderTrader := layout.askOwner orderIndex
          let resting := layout.askOrderSize orderIndex
          if orderTrader ≠ traderIndex then
            .error .overflow
          else
            let removed := if requested ≤ resting then requested else resting
            let locked := layout.baseLocked traderIndex
            let free := layout.baseFree traderIndex
            if removed ≤ locked && free ≤ u64Max - removed then
              let remaining := resting - removed
              let nextLocked := locked - removed
              let nextFree := free + removed
              if remaining = 0 then
                let _ := layout.removeAsk price sequence
                let _ := layout.setBaseLocked traderIndex nextLocked
                let _ := layout.setBaseFree traderIndex nextFree
                .ok removed
              else
                let _ := layout.setAskOrderSize orderIndex remaining
                let _ := layout.setBaseLocked traderIndex nextLocked
                let _ := layout.setBaseFree traderIndex nextFree
                .ok removed
            else
              .error .overflow
    else
      .error .overflow
  else
    .error .overflow

def reduceBidFreeFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (marketAccount traderAccount traderKey0 price sequence requested : UInt64) :
    Except Error UInt64 :=
  if profileAccountBytesAt marketAccount = UInt64.ofNat layout.accountBytes &&
      allocatorHeadersValidAt marketAccount = 1 then
    if layout.tradersValid = 1 && layout.bidsValid = 1 then
      let traderIndex := layout.findTrader
        traderKey0 (accKeyWord traderAccount 1) (accKeyWord traderAccount 2)
        (accKeyWord traderAccount 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex := layout.findBid price sequence
        if orderIndex = 0 then
          .ok 0
        else
          let orderTrader := layout.bidOwner orderIndex
          let resting := layout.bidOrderSize orderIndex
          if orderTrader ≠ traderIndex then
            .error .overflow
          else
            let removed := if requested ≤ resting then requested else resting
            let baseLotsPerBaseUnit := layout.baseLotsPerBaseUnit
            let tickSize := layout.tickSize
            if baseLotsPerBaseUnit = 0 then
              .error .overflow
            else if price = 0 || tickSize ≤ u64Max / price then
              let quotePerBase := price * tickSize
              if removed = 0 || quotePerBase ≤ u64Max / removed then
                let unlocked := (quotePerBase * removed) / baseLotsPerBaseUnit
                let locked := layout.quoteLocked traderIndex
                let free := layout.quoteFree traderIndex
                if unlocked ≤ locked && free ≤ u64Max - unlocked then
                  let remaining := resting - removed
                  let nextLocked := locked - unlocked
                  let nextFree := free + unlocked
                  if remaining = 0 then
                    let _ := layout.removeBid price sequence
                    let _ := layout.setQuoteLocked traderIndex nextLocked
                    let _ := layout.setQuoteFree traderIndex nextFree
                    .ok removed
                  else
                    let _ := layout.setBidOrderSize orderIndex remaining
                    let _ := layout.setQuoteLocked traderIndex nextLocked
                    let _ := layout.setQuoteFree traderIndex nextFree
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
def reduceFreeFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (marketAccount traderAccount traderKey0 side price sequence requested : UInt64) :
    Except Error UInt64 :=
  if side = 0 then
    reduceBidFreeFunds512At layout marketAccount traderAccount traderKey0 price sequence requested
  else
    reduceAskFreeFunds512At layout marketAccount traderAccount traderKey0 price sequence requested

/-- Compute the bid-side quote lots released by the same pinned market scalars as the reducer. -/
def quoteLotsReleased512At (layout : Examples.Svm.PhoenixV1.Layout) (price removed : UInt64) :
    Except Error UInt64 :=
  let baseLotsPerBaseUnit := layout.baseLotsPerBaseUnit
  let tickSize := layout.tickSize
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
def claimReleasedFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderIndex side released : UInt64) :
    Except Error UInt64 :=
  if side = 0 then
    let free := layout.quoteFree traderIndex
    if released ≤ free then
      let _ := layout.setQuoteFree traderIndex (free - released)
      .ok released
    else
      .error .overflow
  else
    let free := layout.baseFree traderIndex
    if released ≤ free then
      let _ := layout.setBaseFree traderIndex (free - released)
      .ok released
    else
      .error .overflow

/-- Phoenix's static audit sink. Recorder and cancellation facades consume the same descriptor as
compile-time data; no handler reconstructs its positional sink or byte geometry. -/
@[pf_inline] def marketRecorderConfig : ProofForge.Svm.BatchRecorder.Config :=
  { logAccount := 0
    selfEntryTag := 15
    authoritySeed := "log"
    maxBytes := 1246
    headerBytes := 93
    countOffset := 91
    maxRecords := 32 }

/-- Open Phoenix's bounded audit batch. `traderCpiAccount` is external-relative because it is
embedded as a CPI data key; market reads remain physical indexes. The 92-byte payload below plus
the component-owned raw-entry byte is Phoenix's 93-byte audit header. -/
def beginMarketBatchAt (origin marketAccount traderCpiAccount marketSequence : UInt64) : UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.begin marketRecorderConfig
    #[.u8le 1, .u8le origin,
      .u64le marketSequence, .u64le unixTime, .u64le clockSlot,
      .u64le (accKeyWord marketAccount 0), .u64le (accKeyWord marketAccount 1),
      .u64le (accKeyWord marketAccount 2), .u64le (accKeyWord marketAccount 3),
      .accKey traderCpiAccount, .u16le 0]
    (findPda "log")

/-- Append one canonical 35-byte Phoenix Reduce record. `orderIndex = 0` disables the append while
leaving `finishMarketBatch` responsible for the required header-only CPI. -/
def recordReduceAt (orderIndex orderSequence price removed remaining : UInt64) : UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.append marketRecorderConfig orderIndex
    #[.u8le 4, .u16le 0, .u64le orderSequence, .u64le price,
      .u64le removed, .u64le remaining]

/-- Append one canonical 43-byte Phoenix Place record. The explicit event index lets PostOnly use
index zero while a remainder posted after Fill and FillSummary uses index two. The two client-id
words preserve the original little-endian u128 wire order without a dynamic source buffer. -/
def recordPlaceAt (eventIndex orderSequence clientIdLow clientIdHigh price baseLots : UInt64) :
    UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.append marketRecorderConfig 1
    #[.u8le 3, .u16le eventIndex, .u64le orderSequence, .u64le clientIdLow,
      .u64le clientIdHigh, .u64le price, .u64le baseLots]

/-- Append one 67-byte Fill event at the caller's bounded traversal index. The maker key is read
from the generic four-word map key projection before its resting order is removed. -/
def recordFillAt (eventIndex makerKey0 makerKey1 makerKey2 makerKey3 orderSequence price filled
    remaining : UInt64) : UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.append marketRecorderConfig 1
    #[.u8le 2, .u16le eventIndex, .u64le makerKey0, .u64le makerKey1,
      .u64le makerKey2, .u64le makerKey3, .u64le orderSequence, .u64le price,
      .u64le filled, .u64le remaining]

/-- Append the aggregate 43-byte taker FillSummary after a bounded matching pass. -/
def recordFillSummaryAt (eventIndex clientIdLow clientIdHigh baseFilled quoteFilled fee : UInt64) :
    UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.append marketRecorderConfig 1
    #[.u8le 6, .u16le eventIndex, .u64le clientIdLow, .u64le clientIdHigh,
      .u64le baseFilled, .u64le quoteFilled, .u64le fee]

/-- Flush Phoenix's current batch, including an empty header-only batch, and close the recorder. -/
def finishMarketBatch : UInt64 :=
  ProofForge.Svm.BatchRecorder.Source.finish marketRecorderConfig

/-- Phoenix-v1 owns this raw instruction's concrete account order. The Token SDK descriptor gives
those positions reusable source roles and erases back to the canonical unchecked transfer metas. -/
@[pf_inline] def quoteWithdrawTokenAccounts :
    ProofForge.Svm.Sdk.Token.UncheckedTransferAccounts :=
  .at 7 6 4 6

@[pf_inline] def baseWithdrawTokenAccounts :
    ProofForge.Svm.Sdk.Token.UncheckedTransferAccounts :=
  .at 7 5 3 5

/-- Execute only the side-selected nonzero classic Token withdrawal. The mint seed points directly
at the authenticated fixed MarketHeader field; no mint account, heap buffer, or copied seed exists. -/
def withdrawReleasedAt (side atoms : UInt64) : UInt64 :=
  if atoms = 0 then
    0
  else if side = 0 then
    let seeds : Array PdaSeed := #[.ascii "vault", .accKey 1, .accData 1 128 32]
    ProofForge.Svm.Sdk.Token.transferSignedWith quoteWithdrawTokenAccounts atoms seeds
      (highUInt32 (accDataWord 2 15))
  else
    let seeds : Array PdaSeed := #[.ascii "vault", .accKey 1, .accData 1 48 32]
    ProofForge.Svm.Sdk.Token.transferSignedWith baseWithdrawTokenAccounts atoms seeds
      (highUInt32 (accDataWord 2 5))

/-- Complete dominating validation required by the component-owned CancelAll mutation loop. The
three fixed allocators, trader key tree, and both FIFO trees are validated before the recorder can
emit or any account byte can change. A missing trader remains distinct: this function succeeds and
the subsequent bounded find returns the zero sentinel. -/
def cancelAllStorageValid512At (marketAccount : UInt64) : UInt64 :=
  let layout := Examples.Svm.PhoenixV1.small 2
  if marketAccount = UInt64.ofNat layout.account &&
      profileAccountBytesAt marketAccount = UInt64.ofNat layout.accountBytes &&
      layout.orderSequence ≠ 0 &&
      allocatorHeadersValidAt marketAccount = 1 then
    if layout.tradersValid = 1 && layout.bidsValid = 1 && layout.asksValid = 1 then 1 else 0
  else
    0

/-- Find the official one-based trader slot after `cancelAllStorageValid512At` has dominated the
operation. Zero is the account-resident null sentinel and implements missing-trader success. -/
def cancelAllTraderIndex512At (marketAccount traderAccount : UInt64) : UInt64 :=
  let layout := Examples.Svm.PhoenixV1.small 2
  if marketAccount = UInt64.ofNat layout.account && traderAccount = 3 then
    layout.findTrader (signerKey traderAccount) (accKeyWord traderAccount 1)
      (accKeyWord traderAccount 2) (accKeyWord traderAccount 3)
  else
    0

/-- Open the invocation-local scalar accumulator shared by both FIFO passes. -/
def beginCancelAll : UInt64 := ProofForge.Svm.FifoCancel.Source.begin

/-- Cancel owned bids in Phoenix logical FIFO order. Static account geometry, collateral math, and
audit recording are owned by the bounded component rather than the generic SVM operation set. -/
def cancelAllBids512At (layout : Examples.Svm.PhoenixV1.Layout) (traderIndex : UInt64) : UInt64 :=
  ProofForge.Svm.FifoCancel.Source.cancelSide
    (layout.bidCancelConfig marketRecorderConfig) traderIndex

/-- Cancel owned asks after the bid pass, preserving one invocation-global event index. -/
def cancelAllAsks512At (layout : Examples.Svm.PhoenixV1.Layout) (traderIndex : UInt64) : UInt64 :=
  ProofForge.Svm.FifoCancel.Source.cancelSide
    (layout.askCancelConfig marketRecorderConfig) traderIndex

/-- Cancel a bounded bid prefix. Search counts every traversed order before owner/price filters;
cancel counts only selected orders. `claimImmediately` is a compile-time adapter choice. -/
def cancelUpToBids512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderIndex tickLimit searchLimit cancelLimit : UInt64)
    (claimImmediately : Bool) : UInt64 :=
  ProofForge.Svm.FifoCancel.Source.cancelUpTo
    (layout.bidCancelConfig marketRecorderConfig)
    traderIndex tickLimit searchLimit cancelLimit claimImmediately

/-- Cancel a bounded ask prefix with the same account-resident cursor contract. -/
def cancelUpToAsks512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderIndex tickLimit searchLimit cancelLimit : UInt64)
    (claimImmediately : Bool) : UInt64 :=
  ProofForge.Svm.FifoCancel.Source.cancelUpTo
    (layout.askCancelConfig marketRecorderConfig)
    traderIndex tickLimit searchLimit cancelLimit claimImmediately

/-- Close the FIFO accumulator after all aggregate results have been consumed. -/
def finishCancelAll : UInt64 := ProofForge.Svm.FifoCancel.Source.finish

/-- Official Phoenix `CancelOrderParams` leaf: `side:u8 || price:u64 || sequence:u64`. -/
structure CancelOrderParams where
  side : UInt8
  price : UInt64
  sequence : UInt64
  deriving Inhabited, Repr, DecidableEq

/-- Shared official Token-context gate for tags 4 and 6. It authenticates the fixed raw account
shape, market status, classic SPL Token program, trader destinations, vault keys, mints, and vault
authorities before either storage mutation or CPI can occur. -/
def cancelWithdrawContextValid : UInt64 :=
  let layout := Examples.Svm.PhoenixV1.small 2
  if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      isWritable 4 = 0 || isWritable 5 = 0 || isWritable 6 = 0 || isWritable 7 = 0 ||
      isWritable 8 ≠ 0 || checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
    0
  else if profileAccountBytesAt 2 ≠ UInt64.ofNat layout.accountBytes then
    0
  else if reduceStatusValidAt 2 = 0 then
    0
  else if Program.classicToken.validWord (Account.Handle.at 8) = 0 then
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

/-- Authenticate the five-account tag-3 context. PDA indexes are relative to the external region
after the executable program prefix: log is 0, market is 1, trader is 2, and seat is 3. The seat
itself remains a fixed 128-byte Phoenix-owned record and carries no heap-backed identity. -/
def placeFreeFundsContextValid : UInt64 :=
  if isWritable 0 ≠ 0 || isWritable 1 ≠ 0 || isWritable 2 = 0 ||
      isWritable 3 ≠ 0 || isWritable 4 ≠ 0 ||
      checkPdaSeeds 0 #[.ascii "log"] ≠ 0 ||
      checkPdaSeeds 3 #[.ascii "seat", .accKey 1, .accKey 2] ≠ 0 then
    0
  else if accDataLen 4 ≠ 128 || ownerIsSelf 4 ≠ 0 ||
      accDataWord 4 0 ≠ seatDiscriminant || accDataWord 4 9 ≠ 1 then
    0
  else if !key4Equal
      (accDataWord 4 1) (accDataWord 4 2) (accDataWord 4 3) (accDataWord 4 4)
      (accKeyWord 2 0) (accKeyWord 2 1) (accKeyWord 2 2) (accKeyWord 2 3) then
    0
  else if !key4Equal
      (accDataWord 4 5) (accDataWord 4 6) (accDataWord 4 7) (accDataWord 4 8)
      (accKeyWord 3 0) (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3) then
    0
  else
    1

/--
Place the bounded tag-3 subset after the entry adapter has authenticated its fixed wire and seat.
The opposite book must be empty and the selected book must have spare capacity, so PostOnly never
matches, reprices, expires, or evicts. The complete trader/bid/ask envelope dominates every write;
the live trader supplies all collateral, the FIFO key consumes word 106 exactly once, and audit
sequencing consumes header word 34 independently. Persistent state remains account-resident
one-based indexes plus the zero sentinel.
-/
def placePostOnlyFreeFunds512At (marketAccount traderAccount side price baseLots clientIdLow
    clientIdHigh : UInt64) : Except Error UInt64 := do
  let layout := Examples.Svm.PhoenixV1.small 2
  if marketAccount ≠ 2 || traderAccount ≠ 3 ||
      cancelAllStorageValid512At marketAccount = 0 || price = 0 || baseLots = 0 then
    .error .overflow
  else
    let status := layout.status
    let bid := side = 0
    let selectedSize :=
      if bid then layout.bidSize else layout.askSize
    let oppositeSize :=
      if bid then layout.askSize else layout.bidSize
    let orderSequence := layout.orderSequence
    let marketSequence := layout.marketSequence
    if (status ≠ 1 && status ≠ 2) || selectedSize ≥ 512 || oppositeSize ≠ 0 ||
        orderSequence = 0 || orderSequence ≥ maxOrderSequence || marketSequence = u64Max then
      .error .overflow
    else
      let traderIndex := layout.findTrader
        (signerKey traderAccount) (accKeyWord traderAccount 1)
        (accKeyWord traderAccount 2) (accKeyWord traderAccount 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let encodedSequence := if bid then ~~~orderSequence else orderSequence
        let duplicate :=
          if bid then
            layout.findBid price encodedSequence
          else
            layout.findAsk price encodedSequence
        if duplicate ≠ 0 then
          .error .overflow
        else if bid then
          let quoteLots ← quoteLotsReleased512At layout price baseLots
          if quoteLots = 0 then
            .error .overflow
          else
            let locked := layout.quoteLocked traderIndex
            let free := layout.quoteFree traderIndex
            if quoteLots > free || locked > u64Max - quoteLots then
              .error .overflow
            else
              let _ := layout.insertBid price encodedSequence traderIndex baseLots 0 0
              let _ := layout.setQuoteLocked traderIndex (locked + quoteLots)
              let _ := layout.setQuoteFree traderIndex (free - quoteLots)
              let _ := layout.setOrderSequence (orderSequence + 1)
              let _ := layout.setMarketSequence (marketSequence + 1)
              let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
              let _ := recordPlaceAt 0 encodedSequence clientIdLow clientIdHigh price baseLots
              let _ := finishMarketBatch
              .ok encodedSequence
        else
          let locked := layout.baseLocked traderIndex
          let free := layout.baseFree traderIndex
          if baseLots > free || locked > u64Max - baseLots then
            .error .overflow
          else
            let _ := layout.insertAsk price encodedSequence traderIndex baseLots 0 0
            let _ := layout.setBaseLocked traderIndex (locked + baseLots)
            let _ := layout.setBaseFree traderIndex (free - baseLots)
            let _ := layout.setOrderSequence (orderSequence + 1)
            let _ := layout.setMarketSequence (marketSequence + 1)
            let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
            let _ := recordPlaceAt 0 encodedSequence clientIdLow clientIdHigh price baseLots
            let _ := finishMarketBatch
            .ok encodedSequence

/-- Compute adjusted quote lots after the caller has established the two multiplication bounds.
This is invocation-local scalar arithmetic; it does not allocate or materialize a quote object. -/
def adjustedQuoteLots512At (layout : Examples.Svm.PhoenixV1.Layout) (price baseLots : UInt64) :
    UInt64 :=
  price * layout.tickSize * baseLots

/-- Spec-facing pure fee formula (same arithmetic as `takerFeeQuoteLots512At`, explicit params). -/
def takerFeeQuoteLotsOf (adjustedQuote bps baseLotsPerBaseUnit : UInt64) : UInt64 :=
  if adjustedQuote = 0 || bps = 0 then
    0
  else
    let adjustedFee := (adjustedQuote * bps + 9999) / 10000
    let whole := adjustedFee / baseLotsPerBaseUnit
    if adjustedFee % baseLotsPerBaseUnit = 0 then whole else whole + 1

/-- Phoenix's aggregate taker fee: ceil at basis-point precision, then ceil to one quote lot. -/
def takerFeeQuoteLots512At (layout : Examples.Svm.PhoenixV1.Layout)
    (adjustedQuote : UInt64) : UInt64 :=
  let bps := layout.takerFeeBps
  let baseLotsPerBaseUnit := layout.baseLotsPerBaseUnit
  if adjustedQuote = 0 || bps = 0 then
    0
  else
    let adjustedFee := (adjustedQuote * bps + 9999) / 10000
    let whole := adjustedFee / baseLotsPerBaseUnit
    if adjustedFee % baseLotsPerBaseUnit = 0 then whole else whole + 1

/-- Compute posting collateral without exposing unchecked multiplication to the non-posting path.
Zero is the fail-closed result for an empty request, invalid lot geometry, overflow, or a sub-lot
quote. This remains Phoenix policy above the generic fixed-record storage SDK. -/
def postingQuoteLotsOrZero512At (price tickSize baseLots baseLotsPerBaseUnit : UInt64) : UInt64 :=
  if price = 0 || tickSize = 0 || baseLots = 0 || baseLotsPerBaseUnit = 0 ||
      tickSize > u64Max / price then
    0
  else if price * tickSize > u64Max / baseLots then
    0
  else
    (price * tickSize * baseLots) / baseLotsPerBaseUnit

/-- Validate the remainder-posting shape one gate at a time so account-storage queries retain their
effect order without consuming scalar-frame locals. The successor is the cursor value produced by
the completed two-maker preflight; no node pointer survives a mutation. -/
def twoMatchPostingValid512At (layout : Examples.Svm.PhoenixV1.Layout) (bid : Bool)
    (price orderSequence nextOrder remainingBaseLots tickSize baseLotsPerBaseUnit : UInt64) :
    UInt64 :=
  if remainingBaseLots = 0 then
    1
  else if orderSequence = 0 || orderSequence ≥ maxOrderSequence then
    0
  else if (if bid then layout.bidSize else layout.askSize) ≥ 512 then
    0
  else if (if bid then layout.findBid price (~~~orderSequence)
      else layout.findAsk price orderSequence) ≠ 0 then
    0
  else if nextOrder = 0 then
    if bid && postingQuoteLotsOrZero512At
        price tickSize remainingBaseLots baseLotsPerBaseUnit = 0 then 0 else 1
  else if (if bid then layout.asks.price nextOrder ≤ price
      else layout.bids.price nextOrder ≥ price) then
    0
  else if (if bid then layout.asks.lastSlotAt nextOrder
      else layout.bids.lastSlotAt nextOrder) ≠ 0 then
    0
  else if (if bid then layout.asks.lastTimeAt nextOrder
      else layout.bids.lastTimeAt nextOrder) ≠ 0 then
    0
  else if bid && postingQuoteLotsOrZero512At
      price tickSize remainingBaseLots baseLotsPerBaseUnit = 0 then
    0
  else
    1

/-!
This bounded Limit slice performs one maker match. Generic SDK components provide validated
best-order cursoring, fixed-record reads/writes, key extraction, insertion/removal, and balance
fields; Phoenix keeps crossing, fee, collateral, self-trade, audit, and packet policy here in
`Examples`. With `match_limit=Some(1)`, no TIF, and `Abort`, the taker may exhaust its budget, or it
may fully consume one maker and post a noncrossing remainder when its own side has spare capacity.
A larger maker remains at the same one-based slot with its size reduced in place. Full-book
eviction and a still-crossing remainder remain outside this bounded slice.
-/
def placeLimitOneMatchFreeFunds512At (marketAccount traderAccount side price baseLots clientIdLow
    clientIdHigh : UInt64) : Except Error UInt64 := do
  let layout := Examples.Svm.PhoenixV1.small 2
  if marketAccount ≠ 2 || traderAccount ≠ 3 ||
      cancelAllStorageValid512At marketAccount = 0 || price = 0 || baseLots = 0 then
    .error .overflow
  else
    let status := layout.status
    let marketSequence := layout.marketSequence
    let orderSequence := layout.orderSequence
    let bid := side = 0
    let selectedSize := if bid then layout.bidSize else layout.askSize
    if (status ≠ 1 && status ≠ 2) || marketSequence = u64Max ||
        orderSequence = 0 || orderSequence ≥ maxOrderSequence then
      .error .overflow
    else
      let taker := layout.findTrader
        (signerKey traderAccount) (accKeyWord traderAccount 1)
        (accKeyWord traderAccount 2) (accKeyWord traderAccount 3)
      if taker = 0 then
        .error .overflow
      else
        let makerOrder :=
          if bid then layout.asks.cursor 0 0 0 else layout.bids.cursor 0 0 0
        if makerOrder = 0 then
          .error .overflow
        else
          let makerPrice :=
            if bid then layout.asks.price makerOrder else layout.bids.price makerOrder
          let makerSequence :=
            if bid then layout.asks.sequence makerOrder else layout.bids.sequence makerOrder
          let maker :=
            if bid then layout.asks.ownerAt makerOrder else layout.bids.ownerAt makerOrder
          let makerSize :=
            if bid then layout.asks.sizeAt makerOrder else layout.bids.sizeAt makerOrder
          let lastSlot :=
            if bid then layout.asks.lastSlotAt makerOrder else layout.bids.lastSlotAt makerOrder
          let lastTime :=
            if bid then layout.asks.lastTimeAt makerOrder else layout.bids.lastTimeAt makerOrder
          let crosses := if bid then makerPrice ≤ price else makerPrice ≥ price
          if !crosses || maker = 0 || maker = taker || makerSize = 0 ||
              lastSlot ≠ 0 || lastTime ≠ 0 then
            .error .overflow
          else
            let matchedBaseLots := if makerSize < baseLots then makerSize else baseLots
            let makerRemaining := makerSize - matchedBaseLots
            let takerRemaining := baseLots - matchedBaseLots
            let shouldPost := takerRemaining ≠ 0
            let encodedSequence :=
              if shouldPost then if bid then ~~~orderSequence else orderSequence else 0
            let duplicate :=
              if !shouldPost then 0
              else if bid then layout.findBid price encodedSequence
              else layout.findAsk price encodedSequence
            let nextMaker :=
              if !shouldPost then 0
              else if bid then layout.asks.cursor 1 makerPrice makerSequence
              else layout.bids.cursor 1 makerPrice makerSequence
            let nextPrice :=
              if nextMaker = 0 then 0
              else if bid then layout.asks.price nextMaker else layout.bids.price nextMaker
            let nextLastSlot :=
              if nextMaker = 0 then 0
              else if bid then layout.asks.lastSlotAt nextMaker
              else layout.bids.lastSlotAt nextMaker
            let nextLastTime :=
              if nextMaker = 0 then 0
              else if bid then layout.asks.lastTimeAt nextMaker
              else layout.bids.lastTimeAt nextMaker
            let nextCrosses :=
              nextMaker ≠ 0 && if bid then nextPrice ≤ price else nextPrice ≥ price
            let postedQuoteLots ←
              if bid && shouldPost then
                quoteLotsReleased512At layout price takerRemaining
              else
                .ok 0
            let invalidPosting := shouldPost &&
              (selectedSize ≥ 512 || duplicate ≠ 0 || nextCrosses ||
                nextLastSlot ≠ 0 || nextLastTime ≠ 0)
            let tickSize := layout.tickSize
            let baseLotsPerBaseUnit := layout.baseLotsPerBaseUnit
            if invalidPosting || (bid && shouldPost && postedQuoteLots = 0) ||
                tickSize = 0 || tickSize > u64Max / makerPrice then
              .error .overflow
            else
              let quotePerBase := makerPrice * tickSize
              if quotePerBase > u64Max / matchedBaseLots then
                .error .overflow
              else
                let adjustedQuote := adjustedQuoteLots512At layout makerPrice matchedBaseLots
                let bps := layout.takerFeeBps
                if baseLotsPerBaseUnit = 0 || bps > 10000 ||
                    (bps ≠ 0 && adjustedQuote > (u64Max - 9999) / bps) ||
                    adjustedQuote % baseLotsPerBaseUnit ≠ 0 then
                  .error .overflow
                else
                  let quoteLots := adjustedQuote / baseLotsPerBaseUnit
                  let fee := takerFeeQuoteLots512At layout adjustedQuote
                  let unclaimedFees := layout.unclaimedQuoteFees
                  if unclaimedFees > u64Max - fee then
                    .error .overflow
                  else
                    if bid then
                      let makerLocked := layout.baseLocked maker
                      let makerFree := layout.quoteFree maker
                      let takerQuoteFree := layout.quoteFree taker
                      let takerBaseFree := layout.baseFree taker
                      if quoteLots > u64Max - fee then
                        .error .overflow
                      else
                        let takerCost := quoteLots + fee
                        if makerLocked < matchedBaseLots || makerFree > u64Max - quoteLots ||
                            takerBaseFree > u64Max - matchedBaseLots then
                          .error .overflow
                        else if shouldPost then
                          let takerQuoteLocked := layout.quoteLocked taker
                          if takerCost > u64Max - postedQuoteLots ||
                              takerQuoteFree < takerCost + postedQuoteLots ||
                              takerQuoteLocked > u64Max - postedQuoteLots then
                            .error .overflow
                          else
                            let makerKey0 := layout.traderKey0 maker
                            let makerKey1 := layout.traderKey1 maker
                            let makerKey2 := layout.traderKey2 maker
                            let makerKey3 := layout.traderKey3 maker
                            let _ := layout.setAskOrderSizeOrRemove makerOrder makerPrice makerSequence
                              makerRemaining
                            let _ := layout.setBaseLocked maker (makerLocked - matchedBaseLots)
                            let _ := layout.setQuoteFree maker (makerFree + quoteLots)
                            let _ := layout.insertBid price encodedSequence taker takerRemaining 0 0
                            let _ := layout.setQuoteLocked taker
                              (takerQuoteLocked + postedQuoteLots)
                            let _ := layout.setQuoteFree taker
                              (takerQuoteFree - takerCost - postedQuoteLots)
                            let _ := layout.setBaseFree taker (takerBaseFree + matchedBaseLots)
                            let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                            let _ := layout.setOrderSequence (orderSequence + 1)
                            let _ := layout.setMarketSequence (marketSequence + 1)
                            let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                            let _ := recordFillAt 0 makerKey0 makerKey1 makerKey2 makerKey3
                              makerSequence makerPrice matchedBaseLots makerRemaining
                            let _ := recordFillSummaryAt 1 clientIdLow clientIdHigh
                              matchedBaseLots takerCost fee
                            let _ := recordPlaceAt 2 encodedSequence clientIdLow clientIdHigh
                              price takerRemaining
                            let _ := finishMarketBatch
                            .ok encodedSequence
                        else if takerQuoteFree < takerCost then
                          .error .overflow
                        else
                          let makerKey0 := layout.traderKey0 maker
                          let makerKey1 := layout.traderKey1 maker
                          let makerKey2 := layout.traderKey2 maker
                          let makerKey3 := layout.traderKey3 maker
                          let _ := layout.setAskOrderSizeOrRemove makerOrder makerPrice makerSequence
                            makerRemaining
                          let _ := layout.setBaseLocked maker (makerLocked - matchedBaseLots)
                          let _ := layout.setQuoteFree maker (makerFree + quoteLots)
                          let _ := layout.setQuoteFree taker (takerQuoteFree - takerCost)
                          let _ := layout.setBaseFree taker (takerBaseFree + matchedBaseLots)
                          let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                          let _ := layout.setMarketSequence (marketSequence + 1)
                          let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                          let _ := recordFillAt 0 makerKey0 makerKey1 makerKey2 makerKey3
                            makerSequence makerPrice matchedBaseLots makerRemaining
                          let _ := recordFillSummaryAt 1 clientIdLow clientIdHigh
                            matchedBaseLots takerCost fee
                          let _ := finishMarketBatch
                          .ok 0
                    else
                      let makerLocked := layout.quoteLocked maker
                      let makerFree := layout.baseFree maker
                      let takerBaseFree := layout.baseFree taker
                      let takerQuoteFree := layout.quoteFree taker
                      if fee > quoteLots || makerLocked < quoteLots ||
                          makerFree > u64Max - matchedBaseLots ||
                          takerQuoteFree > u64Max - (quoteLots - fee) then
                        .error .overflow
                      else if shouldPost then
                        let takerBaseLocked := layout.baseLocked taker
                        if takerBaseFree < baseLots ||
                            takerBaseLocked > u64Max - takerRemaining then
                          .error .overflow
                        else
                          let takerProceeds := quoteLots - fee
                          let makerKey0 := layout.traderKey0 maker
                          let makerKey1 := layout.traderKey1 maker
                          let makerKey2 := layout.traderKey2 maker
                          let makerKey3 := layout.traderKey3 maker
                          let _ := layout.setBidOrderSizeOrRemove makerOrder makerPrice makerSequence
                            makerRemaining
                          let _ := layout.setQuoteLocked maker (makerLocked - quoteLots)
                          let _ := layout.setBaseFree maker (makerFree + matchedBaseLots)
                          let _ := layout.insertAsk price encodedSequence taker takerRemaining 0 0
                          let _ := layout.setBaseLocked taker (takerBaseLocked + takerRemaining)
                          let _ := layout.setBaseFree taker (takerBaseFree - baseLots)
                          let _ := layout.setQuoteFree taker (takerQuoteFree + takerProceeds)
                          let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                          let _ := layout.setOrderSequence (orderSequence + 1)
                          let _ := layout.setMarketSequence (marketSequence + 1)
                          let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                          let _ := recordFillAt 0 makerKey0 makerKey1 makerKey2 makerKey3
                            makerSequence makerPrice matchedBaseLots makerRemaining
                          let _ := recordFillSummaryAt 1 clientIdLow clientIdHigh
                            matchedBaseLots takerProceeds fee
                          let _ := recordPlaceAt 2 encodedSequence clientIdLow clientIdHigh
                            price takerRemaining
                          let _ := finishMarketBatch
                          .ok encodedSequence
                      else if takerBaseFree < matchedBaseLots then
                        .error .overflow
                      else
                        let takerProceeds := quoteLots - fee
                        let makerKey0 := layout.traderKey0 maker
                        let makerKey1 := layout.traderKey1 maker
                        let makerKey2 := layout.traderKey2 maker
                        let makerKey3 := layout.traderKey3 maker
                        let _ := layout.setBidOrderSizeOrRemove makerOrder makerPrice makerSequence
                          makerRemaining
                        let _ := layout.setQuoteLocked maker (makerLocked - quoteLots)
                        let _ := layout.setBaseFree maker (makerFree + matchedBaseLots)
                        let _ := layout.setBaseFree taker (takerBaseFree - matchedBaseLots)
                        let _ := layout.setQuoteFree taker (takerQuoteFree + takerProceeds)
                        let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                        let _ := layout.setMarketSequence (marketSequence + 1)
                        let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                        let _ := recordFillAt 0 makerKey0 makerKey1 makerKey2 makerKey3
                          makerSequence makerPrice matchedBaseLots makerRemaining
                        let _ := recordFillSummaryAt 1 clientIdLow clientIdHigh
                          matchedBaseLots takerProceeds fee
                        let _ := finishMarketBatch
                        .ok 0

/--
Bounded two-maker Limit traversal built only from ordinary invocation-local scalar frames and the
generic account-storage facade. A read-only pass validates both fills and accumulates adjusted
quote lots before any account write or audit effect. A second fixed pass replays those exact keys,
settles each maker in place, and emits indexed Fill records; taker funds and the aggregate fee are
settled once afterward. Two distinct no-TIF makers may exhaust the taker or leave a remainder that
the strict successor proves no longer crosses; that remainder reuses the same fixed-capacity book,
collateral, sequence, audit, and optional-return components as the one-maker path. Same-trader
aggregation across multiple resting orders, full-book eviction, and a still-crossing remainder
remain fail closed.
-/
def placeLimitTwoMatchesFreeFunds512At (marketAccount traderAccount side price baseLots
    clientIdLow clientIdHigh : UInt64) : Except Error UInt64 := Id.run do
  let layout := Examples.Svm.PhoenixV1.small 2
  if marketAccount ≠ 2 || traderAccount ≠ 3 ||
      cancelAllStorageValid512At marketAccount = 0 || price = 0 || baseLots = 0 then
    .error .overflow
  else
    let status := layout.status
    let marketSequence := layout.marketSequence
    let orderSequence := layout.orderSequence
    let bid := side = 0
    let tickSize := layout.tickSize
    let baseLotsPerBaseUnit := layout.baseLotsPerBaseUnit
    let bps := layout.takerFeeBps
    if (status ≠ 1 && status ≠ 2) || marketSequence = u64Max || tickSize = 0 ||
        baseLotsPerBaseUnit = 0 || bps > 10000 then
      .error .overflow
    else
      let taker := layout.findTrader
        (signerKey traderAccount) (accKeyWord traderAccount 1)
        (accKeyWord traderAccount 2) (accKeyWord traderAccount 3)
      let firstOrder :=
        if bid then layout.asks.cursor 0 0 0 else layout.bids.cursor 0 0 0
      if taker = 0 || firstOrder = 0 then
        .error .overflow
      else
        let mut makerOrder := firstOrder
        let mut remainingBaseLots := baseLots
        let mut totalAdjustedQuote : UInt64 := 0
        let mut fillCount : UInt64 := 0
        let mut valid : UInt64 := 1
        let mut previousMaker : UInt64 := 0
        for _ in [:2] do
          if valid = 1 && remainingBaseLots ≠ 0 then
            if makerOrder = 0 then
              valid := 0
            else
              let makerPrice :=
                if bid then layout.asks.price makerOrder else layout.bids.price makerOrder
              let makerSequence :=
                if bid then layout.asks.sequence makerOrder else layout.bids.sequence makerOrder
              let maker :=
                if bid then layout.asks.ownerAt makerOrder else layout.bids.ownerAt makerOrder
              let makerSize :=
                if bid then layout.asks.sizeAt makerOrder else layout.bids.sizeAt makerOrder
              let lastSlot :=
                if bid then layout.asks.lastSlotAt makerOrder else layout.bids.lastSlotAt makerOrder
              let lastTime :=
                if bid then layout.asks.lastTimeAt makerOrder else layout.bids.lastTimeAt makerOrder
              let crosses := if bid then makerPrice ≤ price else makerPrice ≥ price
              if !crosses || makerPrice = 0 || maker = 0 || maker = taker || makerSize = 0 ||
                  lastSlot ≠ 0 || lastTime ≠ 0 ||
                  (fillCount ≠ 0 && maker = previousMaker) then
                valid := 0
              else if tickSize > u64Max / makerPrice then
                valid := 0
              else
                let matchedBaseLots :=
                  if makerSize < remainingBaseLots then makerSize else remainingBaseLots
                let quotePerBase := makerPrice * tickSize
                if quotePerBase > u64Max / matchedBaseLots then
                  valid := 0
                else
                  let adjustedQuote := quotePerBase * matchedBaseLots
                  if adjustedQuote % baseLotsPerBaseUnit ≠ 0 ||
                      totalAdjustedQuote > u64Max - adjustedQuote then
                    valid := 0
                  else
                    let quoteLots := adjustedQuote / baseLotsPerBaseUnit
                    if bid then
                      let makerLocked := layout.baseLocked maker
                      let makerFree := layout.quoteFree maker
                      if makerLocked < matchedBaseLots || makerFree > u64Max - quoteLots then
                        valid := 0
                      else
                        let nextOrder := layout.asks.cursor 1 makerPrice makerSequence
                        makerOrder := nextOrder
                        remainingBaseLots := remainingBaseLots - matchedBaseLots
                        totalAdjustedQuote := totalAdjustedQuote + adjustedQuote
                        fillCount := fillCount + 1
                        previousMaker := maker
                    else
                      let makerLocked := layout.quoteLocked maker
                      let makerFree := layout.baseFree maker
                      if makerLocked < quoteLots || makerFree > u64Max - matchedBaseLots then
                        valid := 0
                      else
                        let nextOrder := layout.bids.cursor 1 makerPrice makerSequence
                        makerOrder := nextOrder
                        remainingBaseLots := remainingBaseLots - matchedBaseLots
                        totalAdjustedQuote := totalAdjustedQuote + adjustedQuote
                        fillCount := fillCount + 1
                        previousMaker := maker
        if valid = 0 || fillCount ≠ 2 then
          .error .overflow
        else
          if twoMatchPostingValid512At layout bid price orderSequence makerOrder
                remainingBaseLots tickSize baseLotsPerBaseUnit = 0 ||
              (bps ≠ 0 && totalAdjustedQuote > (u64Max - 9999) / bps) then
            .error .overflow
          else
            let fee := takerFeeQuoteLots512At layout totalAdjustedQuote
            let unclaimedFees := layout.unclaimedQuoteFees
            if unclaimedFees > u64Max - fee then
              .error .overflow
            else if bid then
              if totalAdjustedQuote / baseLotsPerBaseUnit > u64Max - fee then
                .error .overflow
              else
                let takerCost := totalAdjustedQuote / baseLotsPerBaseUnit + fee
                let takerQuoteFree := layout.quoteFree taker
                let takerBaseFree := layout.baseFree taker
                if takerCost > u64Max -
                      postingQuoteLotsOrZero512At
                        price tickSize remainingBaseLots baseLotsPerBaseUnit ||
                    takerQuoteFree < takerCost +
                      postingQuoteLotsOrZero512At
                        price tickSize remainingBaseLots baseLotsPerBaseUnit ||
                    layout.quoteLocked taker > u64Max -
                      postingQuoteLotsOrZero512At
                        price tickSize remainingBaseLots baseLotsPerBaseUnit ||
                    takerBaseFree > u64Max - (baseLots - remainingBaseLots) then
                  .error .overflow
                else
                  let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                  let mut applyOrder := firstOrder
                  let mut applyRemaining := baseLots
                  for _ in [:2] do
                    let eventIndex : UInt64 := if applyRemaining = baseLots then 0 else 1
                    let makerPrice := layout.asks.price applyOrder
                    let makerSequence := layout.asks.sequence applyOrder
                    let maker := layout.asks.ownerAt applyOrder
                    let makerSize := layout.asks.sizeAt applyOrder
                    let matchedBaseLots :=
                      if makerSize < applyRemaining then makerSize else applyRemaining
                    let makerRemaining := makerSize - matchedBaseLots
                    let quoteLots := adjustedQuoteLots512At layout makerPrice matchedBaseLots /
                      baseLotsPerBaseUnit
                    let nextOrder := layout.asks.cursor 1 makerPrice makerSequence
                    let makerKey0 := layout.traderKey0 maker
                    let makerKey1 := layout.traderKey1 maker
                    let makerKey2 := layout.traderKey2 maker
                    let makerKey3 := layout.traderKey3 maker
                    let makerLocked := layout.baseLocked maker
                    let makerFree := layout.quoteFree maker
                    let _ := layout.setAskOrderSizeOrRemove applyOrder makerPrice makerSequence
                      makerRemaining
                    let _ := layout.setBaseLocked maker (makerLocked - matchedBaseLots)
                    let _ := layout.setQuoteFree maker (makerFree + quoteLots)
                    let _ := recordFillAt eventIndex makerKey0 makerKey1 makerKey2 makerKey3
                      makerSequence makerPrice matchedBaseLots makerRemaining
                    applyOrder := nextOrder
                    applyRemaining := applyRemaining - matchedBaseLots
                  if remainingBaseLots ≠ 0 then
                    let _ := layout.insertBid price (~~~orderSequence) taker
                      remainingBaseLots 0 0
                    let _ := layout.setQuoteLocked taker
                      (layout.quoteLocked taker +
                        postingQuoteLotsOrZero512At
                          price tickSize remainingBaseLots baseLotsPerBaseUnit)
                    let _ := layout.setQuoteFree taker
                      (takerQuoteFree - takerCost -
                        postingQuoteLotsOrZero512At
                          price tickSize remainingBaseLots baseLotsPerBaseUnit)
                    let _ := layout.setBaseFree taker
                      (takerBaseFree + (baseLots - remainingBaseLots))
                    let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                    let _ := layout.setOrderSequence (orderSequence + 1)
                    let _ := layout.setMarketSequence (marketSequence + 1)
                    let _ := recordFillSummaryAt fillCount clientIdLow clientIdHigh
                      (baseLots - remainingBaseLots) takerCost fee
                    let _ := recordPlaceAt (fillCount + 1) (~~~orderSequence)
                      clientIdLow clientIdHigh price remainingBaseLots
                    let _ := finishMarketBatch
                    .ok (~~~orderSequence)
                  else
                    let _ := layout.setQuoteFree taker (takerQuoteFree - takerCost)
                    let _ := layout.setBaseFree taker
                      (takerBaseFree + (baseLots - remainingBaseLots))
                    let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                    let _ := layout.setMarketSequence (marketSequence + 1)
                    let _ := recordFillSummaryAt fillCount clientIdLow clientIdHigh
                      (baseLots - remainingBaseLots) takerCost fee
                    let _ := finishMarketBatch
                    .ok 0
            else if fee > totalAdjustedQuote / baseLotsPerBaseUnit then
              .error .overflow
            else
              let takerProceeds := totalAdjustedQuote / baseLotsPerBaseUnit - fee
              let takerBaseFree := layout.baseFree taker
              let takerQuoteFree := layout.quoteFree taker
              if takerBaseFree < baseLots ||
                  layout.baseLocked taker > u64Max - remainingBaseLots ||
                  takerQuoteFree > u64Max - takerProceeds then
                .error .overflow
              else
                let _ := beginMarketBatchAt 3 marketAccount marketAccount marketSequence
                let mut applyOrder := firstOrder
                let mut applyRemaining := baseLots
                for _ in [:2] do
                  let eventIndex : UInt64 := if applyRemaining = baseLots then 0 else 1
                  let makerPrice := layout.bids.price applyOrder
                  let makerSequence := layout.bids.sequence applyOrder
                  let maker := layout.bids.ownerAt applyOrder
                  let makerSize := layout.bids.sizeAt applyOrder
                  let matchedBaseLots :=
                    if makerSize < applyRemaining then makerSize else applyRemaining
                  let makerRemaining := makerSize - matchedBaseLots
                  let quoteLots := adjustedQuoteLots512At layout makerPrice matchedBaseLots /
                    baseLotsPerBaseUnit
                  let nextOrder := layout.bids.cursor 1 makerPrice makerSequence
                  let makerKey0 := layout.traderKey0 maker
                  let makerKey1 := layout.traderKey1 maker
                  let makerKey2 := layout.traderKey2 maker
                  let makerKey3 := layout.traderKey3 maker
                  let makerLocked := layout.quoteLocked maker
                  let makerFree := layout.baseFree maker
                  let _ := layout.setBidOrderSizeOrRemove applyOrder makerPrice makerSequence
                    makerRemaining
                  let _ := layout.setQuoteLocked maker (makerLocked - quoteLots)
                  let _ := layout.setBaseFree maker (makerFree + matchedBaseLots)
                  let _ := recordFillAt eventIndex makerKey0 makerKey1 makerKey2 makerKey3
                    makerSequence makerPrice matchedBaseLots makerRemaining
                  applyOrder := nextOrder
                  applyRemaining := applyRemaining - matchedBaseLots
                if remainingBaseLots ≠ 0 then
                  let _ := layout.insertAsk price orderSequence taker remainingBaseLots 0 0
                  let _ := layout.setBaseLocked taker (layout.baseLocked taker + remainingBaseLots)
                  let _ := layout.setBaseFree taker (takerBaseFree - baseLots)
                  let _ := layout.setQuoteFree taker (takerQuoteFree + takerProceeds)
                  let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                  let _ := layout.setOrderSequence (orderSequence + 1)
                  let _ := layout.setMarketSequence (marketSequence + 1)
                  let _ := recordFillSummaryAt fillCount clientIdLow clientIdHigh
                    (baseLots - remainingBaseLots) takerProceeds fee
                  let _ := recordPlaceAt (fillCount + 1) orderSequence clientIdLow clientIdHigh
                    price remainingBaseLots
                  let _ := finishMarketBatch
                  .ok orderSequence
                else
                  let _ := layout.setBaseFree taker (takerBaseFree - baseLots)
                  let _ := layout.setQuoteFree taker (takerQuoteFree + takerProceeds)
                  let _ := layout.setUnclaimedQuoteFees (unclaimedFees + fee)
                  let _ := layout.setMarketSequence (marketSequence + 1)
                  let _ := recordFillSummaryAt fillCount clientIdLow clientIdHigh
                    (baseLots - remainingBaseLots) takerProceeds fee
                  let _ := finishMarketBatch
                  .ok 0

/-- Historical generated adapters retain their existing account geometry and IDL. -/
@[pf_entry]
def reduceAskFreeFunds512 (s : State) (price sequence requested : UInt64) :
    Except Error (State × UInt64) := do
  let removed ← reduceAskFreeFunds512At (Examples.Svm.PhoenixV1.small 1)
    1 0 (accKeyWord 0 0) price sequence requested
  .ok (s, removed)

@[pf_entry]
def reduceBidFreeFunds512 (s : State) (price sequence requested : UInt64) :
    Except Error (State × UInt64) := do
  let removed ← reduceBidFreeFunds512At (Examples.Svm.PhoenixV1.small 1)
    1 0 (accKeyWord 0 0) price sequence requested
  .ok (s, removed)

/--
Official tag-3 wire, restricted to `OrderPacket::PostOnly`, two canonical `None` time-in-force
markers, deposited funds only, and hard insufficient-funds failure:
`03 || 00 || side || price:u64 || base:u64 || client:u128 || reject || 01 || 00 || 00 || 00`.
The bounded storage transition accepts either canonical reject flag because the opposite book must
be empty. Official Phoenix serializes its collected IDs as a Borsh `Vec<FIFOOrderId>` after all
event CPIs: this strict slice always rests one order, so success is exactly
`01 00 00 00 || price:u64 || encoded_sequence:u64`. The three scalar leaves use a fixed-width
EntryAdapter return plan; no protocol return opcode or runtime allocation is involved.
-/
@[pf_entry, pf_svm_raw_variant_return 3 0 5 0 [4, 8, 8]]
def placeLimitOrderWithFreeFunds (_s : State) (side : UInt8)
    (price baseLots clientIdLow clientIdHigh : UInt64)
    (rejectPostOnly useOnlyDepositedFunds lastValidSlot lastValidUnixTimestamp
      failSilentlyOnInsufficientFunds : UInt8) :
    Except Error (State × (UInt32 × (UInt64 × UInt64))) := do
  if (side ≠ 0 && side ≠ 1) ||
      (rejectPostOnly ≠ 0 && rejectPostOnly ≠ 1) || useOnlyDepositedFunds ≠ 1 ||
      lastValidSlot ≠ 0 || lastValidUnixTimestamp ≠ 0 ||
      failSilentlyOnInsufficientFunds ≠ 0 || placeFreeFundsContextValid = 0 then
    .error .overflow
  else
    let encodedSequence ← placePostOnlyFreeFunds512At 2 3 side.toUInt64 price baseLots
      clientIdLow clientIdHigh
    .ok (_s, ((1 : UInt32), (price, encodedSequence)))

/-- Exact modern `OrderPacket::Limit` slices:
`03 || 01 || side || price || base || Abort || Some(1|2) || client:u128 || 01 || None || None || 00`.
The one-maker path retains partial fills and noncrossing remainder posting. The two-maker path uses
a read-only bounded scalar-frame pass followed by an exact replay, aggregates the taker fee across
both fills, and can post a strict noncrossing remainder through the same fixed-capacity SDK path.
Unsupported match limits, self-trade/TIF policy, same-maker aggregation, still-crossing remainders,
and full-book eviction remain fail closed.
-/
@[pf_entry, pf_svm_raw_variant_optional_return 3 1 5 0 [4, 8, 8]]
def placeLimitOrderWithFreeFundsLimit (_s : State) (side : UInt8)
    (price baseLots : UInt64) (selfTradeBehavior matchLimitPresent : UInt8)
    (matchLimit clientIdLow clientIdHigh : UInt64)
    (useOnlyDepositedFunds lastValidSlotPresent lastValidUnixTimestampPresent
      failSilentlyOnInsufficientFunds : UInt8) :
    Except Error (State × (UInt8 × (UInt32 × (UInt64 × UInt64)))) := do
  if (side ≠ 0 && side ≠ 1) || selfTradeBehavior ≠ 0 || matchLimitPresent ≠ 1 ||
      (matchLimit ≠ 1 && matchLimit ≠ 2) || useOnlyDepositedFunds ≠ 1 ||
      lastValidSlotPresent ≠ 0 ||
      lastValidUnixTimestampPresent ≠ 0 || failSilentlyOnInsufficientFunds ≠ 0 ||
      placeFreeFundsContextValid = 0 then
    .error .overflow
  else if matchLimit = 1 then
    let encodedSequence ← placeLimitOneMatchFreeFunds512At 2 3 side.toUInt64 price baseLots
      clientIdLow clientIdHigh
    let present : UInt8 := if encodedSequence = 0 then 0 else 1
    let length : UInt32 := if encodedSequence = 0 then 0 else 1
    .ok (_s, (present, (length, (price, encodedSequence))))
  else
    let encodedSequence ← placeLimitTwoMatchesFreeFunds512At 2 3 side.toUInt64 price baseLots
      clientIdLow clientIdHigh
    let present : UInt8 := if encodedSequence = 0 then 0 else 1
    let length : UInt32 := if encodedSequence = 0 then 0 else 1
    .ok (_s, (present, (length, (price, encodedSequence))))

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
    let layout := Examples.Svm.PhoenixV1.small 2
    let side := side.toUInt64
    if side ≠ 0 && side ≠ 1 then
      .error .overflow
    else
      let orderIndex :=
        if side = 0 then
          layout.findBid price sequence
        else
          layout.findAsk price sequence
      let resting :=
        if orderIndex = 0 then 0
        else if side = 0 then layout.bidOrderSize orderIndex
        else layout.askOrderSize orderIndex
      let traderKey0 := signerKey 3
      let removed ← reduceFreeFunds512At layout 2 3 traderKey0 side price sequence requested
      let marketSequence := layout.marketSequence
      let remaining := resting - removed
      let _ := layout.setMarketSequence (marketSequence + 1)
      let _ := beginMarketBatchAt 5 2 2 marketSequence
      let _ := recordReduceAt orderIndex sequence price removed remaining
      let _ := finishMarketBatch
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
    let layout := Examples.Svm.PhoenixV1.small 2
    let side := side.toUInt64
    if side ≠ 0 && side ≠ 1 then
      .error .overflow
    else
      let traderKey0 := signerKey 3
      let traderIndex := layout.findTrader
        traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
      if traderIndex = 0 then
        .error .overflow
      else
        let orderIndex :=
          if side = 0 then
            layout.findBid price sequence
          else
            layout.findAsk price sequence
        let resting :=
          if orderIndex = 0 then 0
          else if side = 0 then layout.bidOrderSize orderIndex
          else layout.askOrderSize orderIndex
        let removed := if requested ≤ resting then requested else resting
        let released ←
          if side = 0 then quoteLotsReleased512At layout price removed else .ok removed
        let lotSize := if side = 0 then layout.quoteLotSize else layout.baseLotSize
        let releasedDivisor := if released = 0 then 1 else released
        if lotSize ≤ u64Max / releasedDivisor then
          let atoms := released * lotSize
          let actual ← reduceFreeFunds512At layout 2 3 traderKey0 side price sequence requested
          if actual ≠ removed then
            .error .overflow
          else
            let _ ← claimReleasedFunds512At layout traderIndex side released
            let _ := withdrawReleasedAt side atoms
            let marketSequence := layout.marketSequence
            let _ := layout.setMarketSequence (marketSequence + 1)
            let _ := beginMarketBatchAt 4 2 2 marketSequence
            let _ := recordReduceAt orderIndex sequence price actual (resting - actual)
            let _ := finishMarketBatch
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
    let layout := Examples.Svm.PhoenixV1.small 2
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := layout.marketSequence
    let _ := layout.setMarketSequence (marketSequence + 1)
    let _ := beginMarketBatchAt 7 2 2 marketSequence
    let _ := beginCancelAll
    let _ := cancelAllBids512At layout traderIndex
    let _ := cancelAllAsks512At layout traderIndex
    let _ := finishCancelAll
    let _ := finishMarketBatch
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
    let layout := Examples.Svm.PhoenixV1.small 2
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := layout.marketSequence
    let _ := layout.setMarketSequence (marketSequence + 1)
    let _ := beginMarketBatchAt 6 2 2 marketSequence
    let _ := beginCancelAll
    let _ := cancelAllBids512At layout traderIndex
    let _ := cancelAllAsks512At layout traderIndex
    let quoteReleased := ProofForge.Svm.FifoCancel.Source.quoteReleased
    let baseReleased := ProofForge.Svm.FifoCancel.Source.baseReleased
    let quoteLotSize := layout.quoteLotSize
    let baseLotSize := layout.baseLotSize
    let quoteDivisor := if quoteReleased = 0 then 1 else quoteReleased
    let baseDivisor := if baseReleased = 0 then 1 else baseReleased
    if quoteLotSize ≤ u64Max / quoteDivisor && baseLotSize ≤ u64Max / baseDivisor then
      let quoteAtoms := quoteReleased * quoteLotSize
      let baseAtoms := baseReleased * baseLotSize
      let _ ←
        if traderIndex = 0 then .ok 0
        else claimReleasedFunds512At layout traderIndex 0 quoteReleased
      let _ := withdrawReleasedAt 0 quoteAtoms
      let _ ←
        if traderIndex = 0 then .ok 0
        else claimReleasedFunds512At layout traderIndex 1 baseReleased
      let _ := withdrawReleasedAt 1 baseAtoms
      let _ := finishCancelAll
      let _ := finishMarketBatch
      .ok (_s, 0)
    else
      .error .overflow

/--
Official Phoenix `CancelUpToWithFreeFunds` tag 9 wire:
`09 || side:u8 || Option<u64> || Option<u32> || Option<u32>`. None uses the side-extreme tick and
the selected book's current length. Search is counted before owner/price filters, tick comparison is
inclusive, and only qualifying orders count toward the cancel cap. This four-account path keeps
released collateral in free funds and has no Token/status gate.
-/
@[pf_entry, pf_svm_raw_borsh_options 9 4 0 1 [8, 4, 4]]
def cancelUpToOrdersWithFreeFunds (_s : State) (side tickPresent : UInt8) (tick : UInt64)
    (searchPresent : UInt8) (search : UInt32) (cancelPresent : UInt8)
    (cancel : UInt32) : Except Error (State × UInt64) := do
  if side ≠ 0 && side ≠ 1 then
    .error .overflow
  else if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
    .error .overflow
  else if cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let layout := Examples.Svm.PhoenixV1.small 2
    let bid := side = 0
    let bookSize := if bid then layout.bidSize else layout.askSize
    let tickLimit := if tickPresent = 0 then if bid then 0 else u64Max else tick
    let searchLimit := if searchPresent = 0 then bookSize else search.toUInt64
    let cancelLimit := if cancelPresent = 0 then bookSize else cancel.toUInt64
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := layout.marketSequence
    let _ := layout.setMarketSequence (marketSequence + 1)
    let _ := beginMarketBatchAt 9 2 2 marketSequence
    let _ := beginCancelAll
    if bid then
      let _ := cancelUpToBids512At layout traderIndex tickLimit searchLimit cancelLimit false
      let _ := finishCancelAll
      let _ := finishMarketBatch
      .ok (_s, 0)
    else
      let _ := cancelUpToAsks512At layout traderIndex tickLimit searchLimit cancelLimit false
      let _ := finishCancelAll
      let _ := finishMarketBatch
      .ok (_s, 0)

/--
Official Phoenix `CancelUpTo` tag 8 uses the same bounded selection, but claims each selected
order's released collateral inside the component and withdraws the aggregate through the shared
nine-account classic Token context. Pre-existing free balances are therefore preserved.
-/
@[pf_entry, pf_svm_raw_borsh_options 8 9 0 1 [8, 4, 4]]
def cancelUpToOrders (_s : State) (side tickPresent : UInt8) (tick : UInt64)
    (searchPresent : UInt8) (search : UInt32) (cancelPresent : UInt8)
    (cancel : UInt32) : Except Error (State × UInt64) := do
  if side ≠ 0 && side ≠ 1 then
    .error .overflow
  else if cancelWithdrawContextValid = 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let layout := Examples.Svm.PhoenixV1.small 2
    let bid := side = 0
    let bookSize := if bid then layout.bidSize else layout.askSize
    let tickLimit := if tickPresent = 0 then if bid then 0 else u64Max else tick
    let searchLimit := if searchPresent = 0 then bookSize else search.toUInt64
    let cancelLimit := if cancelPresent = 0 then bookSize else cancel.toUInt64
    let traderIndex := cancelAllTraderIndex512At 2 3
    let marketSequence := layout.marketSequence
    let _ := layout.setMarketSequence (marketSequence + 1)
    let _ := beginMarketBatchAt 8 2 2 marketSequence
    let _ := beginCancelAll
    if bid then
      let _ := cancelUpToBids512At layout traderIndex tickLimit searchLimit cancelLimit true
      let released := ProofForge.Svm.FifoCancel.Source.quoteReleased
      let lotSize := layout.quoteLotSize
      let divisor := if released = 0 then 1 else released
      if lotSize ≤ u64Max / divisor then
        let atoms := released * lotSize
        let _ := withdrawReleasedAt 0 atoms
        let _ := finishCancelAll
        let _ := finishMarketBatch
        .ok (_s, 0)
      else
        .error .overflow
    else
      let _ := cancelUpToAsks512At layout traderIndex tickLimit searchLimit cancelLimit true
      let released := ProofForge.Svm.FifoCancel.Source.baseReleased
      let lotSize := layout.baseLotSize
      let divisor := if released = 0 then 1 else released
      if lotSize ≤ u64Max / divisor then
        let atoms := released * lotSize
        let _ := withdrawReleasedAt 1 atoms
        let _ := finishCancelAll
        let _ := finishMarketBatch
        .ok (_s, 0)
      else
        .error .overflow

/--
Cancel one resting order id for tags 10/11. Side/MSB mismatch, missing id, and foreign owner
are skips that still emit a header-only Reduce (`recordIndex = 0`). Returns removed base lots.
-/
def cancelOneByIdFreeFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderKey0 traderIndex side price sequence : UInt64) : Except Error UInt64 := do
  if side ≠ 0 && side ≠ 1 then
    .error .overflow
  else
    let encodedBid := sequence >>> 63 = 1
    let skip := (side = 0 && !encodedBid) || (side = 1 && encodedBid)
    let orderIndex :=
      if skip || traderIndex = 0 then 0
      else if side = 0 then layout.findBid price sequence
      else layout.findAsk price sequence
    let owner :=
      if orderIndex = 0 then 0
      else if side = 0 then layout.bidOwner orderIndex
      else layout.askOwner orderIndex
    let resting :=
      if orderIndex = 0 || owner ≠ traderIndex then 0
      else if side = 0 then layout.bidOrderSize orderIndex
      else layout.askOrderSize orderIndex
    let removed ←
      if resting = 0 then .ok 0
      else
        reduceFreeFunds512At layout 2 3 traderKey0 side price sequence resting
    let recordIndex := if removed = 0 then 0 else orderIndex
    let _ := recordReduceAt recordIndex sequence price removed 0
    .ok removed

/-- Released lots for one successful cancel-by-id, after removal. -/
def releasedLotsForCancel512At (layout : Examples.Svm.PhoenixV1.Layout)
    (side price removed : UInt64) : Except Error UInt64 :=
  if removed = 0 then .ok 0
  else if side = 0 then quoteLotsReleased512At layout price removed
  else .ok removed

/-- Cancel one id and return released lots (side-aware). Inlined to shrink tag-10 scalar locals
after main's Extract began retaining more sequenced join locals. -/
def cancelOneReleased512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderKey0 traderIndex side price sequence : UInt64) : Except Error UInt64 := do
  let removed ← cancelOneByIdFreeFunds512At layout traderKey0 traderIndex side price sequence
  releasedLotsForCancel512At layout side price removed

/-- Claim aggregated quote/base lots and withdraw atoms for CancelMultiple tag 10.
Keeping this finish helper `pf_inline` collapses duplicated scalar locals across nest arms. -/
def finishCancelMultipleWithdraw512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderIndex quoteReleased baseReleased : UInt64) : Except Error UInt64 := do
  let quoteLotSize := layout.quoteLotSize
  let baseLotSize := layout.baseLotSize
  let quoteDivisor := if quoteReleased = 0 then 1 else quoteReleased
  let baseDivisor := if baseReleased = 0 then 1 else baseReleased
  if quoteLotSize ≤ u64Max / quoteDivisor && baseLotSize ≤ u64Max / baseDivisor then
    let quoteAtoms := quoteReleased * quoteLotSize
    let baseAtoms := baseReleased * baseLotSize
    let _ ←
      if traderIndex = 0 || quoteReleased = 0 then .ok 0
      else claimReleasedFunds512At layout traderIndex 0 quoteReleased
    let _ ←
      if traderIndex = 0 || baseReleased = 0 then .ok 0
      else claimReleasedFunds512At layout traderIndex 1 baseReleased
    let _ := withdrawReleasedAt 0 quoteAtoms
    let _ := withdrawReleasedAt 1 baseAtoms
    let _ := finishMarketBatch
    .ok 0
  else
    .error .overflow

/-- Fold released lots into a quote or base accumulator (`isQuote = 1` → quote). -/
def addReleasedAcc512At (acc side released isQuote : UInt64) : Except Error UInt64 :=
  let add :=
    if isQuote = 0 then (if side = 0 then (0 : UInt64) else released)
    else (if side = 0 then released else 0)
  if acc > u64Max - add then .error .overflow else .ok (acc + add)

/--
Official Phoenix `CancelMultipleOrdersByIdWithFreeFunds` tag 11 wire:
`0b || Borsh Vec<CancelOrderParams>`. This profile slice accepts at most **eight** order ids
(`BoundedVec` capacity = 8; max wire 141 bytes). Empty vectors are a no-op. Each id is cancelled through the shared
per-id helper; collateral stays in free funds.
-/
@[pf_entry, pf_svm_raw 11 4 0]
def cancelMultipleOrdersByIdWithFreeFunds (_s : State)
    (orders : BoundedVec CancelOrderParams 8) : Except Error (State × UInt64) := do
  if orders.length = 0 then
    if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
        checkPdaSeeds 0 #[.ascii "log"] ≠ 0 then
      .error .overflow
    else
      .ok (_s, 0)
  else if isWritable 1 ≠ 0 || isWritable 2 = 0 || isWritable 3 ≠ 0 ||
      checkPdaSeeds 0 #[.ascii "log"] ≠ 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let side0 := orders.values[0]!.side.toUInt64
    let side1ok :=
      orders.length ≤ 1 ||
        orders.values[1]!.side.toUInt64 = 0 ||
        orders.values[1]!.side.toUInt64 = 1
    let side2ok :=
      orders.length ≤ 2 ||
        orders.values[2]!.side.toUInt64 = 0 ||
        orders.values[2]!.side.toUInt64 = 1
    let side3ok :=
      orders.length ≤ 3 ||
        orders.values[3]!.side.toUInt64 = 0 ||
        orders.values[3]!.side.toUInt64 = 1
    let side4ok :=
      orders.length ≤ 4 ||
        orders.values[4]!.side.toUInt64 = 0 ||
        orders.values[4]!.side.toUInt64 = 1
    let side5ok :=
      orders.length ≤ 5 ||
        orders.values[5]!.side.toUInt64 = 0 ||
        orders.values[5]!.side.toUInt64 = 1
    let side6ok :=
      orders.length ≤ 6 ||
        orders.values[6]!.side.toUInt64 = 0 ||
        orders.values[6]!.side.toUInt64 = 1
    let side7ok :=
      orders.length ≤ 7 ||
        orders.values[7]!.side.toUInt64 = 0 ||
        orders.values[7]!.side.toUInt64 = 1
    if (side0 ≠ 0 && side0 ≠ 1) || !side1ok || !side2ok || !side3ok || !side4ok || !side5ok || !side6ok || !side7ok then
      .error .overflow
    else
      let layout := Examples.Svm.PhoenixV1.small 2
      let traderKey0 := signerKey 3
      let traderIndex := layout.findTrader
        traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
      let marketSequence := layout.marketSequence
      let _ := layout.setMarketSequence (marketSequence + 1)
      let _ := beginMarketBatchAt 11 2 2 marketSequence
      let o0 := orders.values[0]!
      let _ ←
        cancelOneByIdFreeFunds512At layout traderKey0 traderIndex side0 o0.price o0.sequence
      if orders.length ≥ 2 then
        let o1 := orders.values[1]!
        let _ ←
          cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
            o1.side.toUInt64 o1.price o1.sequence
        if orders.length ≥ 3 then
          let o2 := orders.values[2]!
          let _ ←
            cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
              o2.side.toUInt64 o2.price o2.sequence
          if orders.length ≥ 4 then
            let o3 := orders.values[3]!
            let _ ←
              cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
                o3.side.toUInt64 o3.price o3.sequence
            if orders.length ≥ 5 then
              let o4 := orders.values[4]!
              let _ ←
                cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
                  o4.side.toUInt64 o4.price o4.sequence
              if orders.length ≥ 6 then
                let o5 := orders.values[5]!
                let _ ←
                  cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
                    o5.side.toUInt64 o5.price o5.sequence
                if orders.length ≥ 7 then
                  let o6 := orders.values[6]!
                  let _ ←
                    cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
                      o6.side.toUInt64 o6.price o6.sequence
                  if orders.length ≥ 8 then
                    let o7 := orders.values[7]!
                    let _ ←
                      cancelOneByIdFreeFunds512At layout traderKey0 traderIndex
                        o7.side.toUInt64 o7.price o7.sequence
                    let _ := finishMarketBatch
                    .ok (_s, 0)
                  else
                    let _ := finishMarketBatch
                    .ok (_s, 0)
                else
                  let _ := finishMarketBatch
                  .ok (_s, 0)
              else
                let _ := finishMarketBatch
                .ok (_s, 0)
            else
              let _ := finishMarketBatch
              .ok (_s, 0)
          else
            let _ := finishMarketBatch
            .ok (_s, 0)
        else
          let _ := finishMarketBatch
          .ok (_s, 0)
      else
        let _ := finishMarketBatch
        .ok (_s, 0)

/--
Official Phoenix `CancelMultipleOrdersById` tag 10 wire uses a eight-id vector, claims any
released collateral, and withdraws through the shared nine-account classic Token context. Quote and
base lots from all ids are aggregated before claim/withdraw (`BoundedVec` capacity = 8; max wire 141).
The scalar/CPI seam at 1216 covers the eighth densified nest under a 9-account frame.
-/
@[pf_entry, pf_svm_raw 10 9 0]
def cancelMultipleOrdersById (_s : State)
    (orders : BoundedVec CancelOrderParams 8) : Except Error (State × UInt64) := do
  if orders.length = 0 then
    if cancelWithdrawContextValid = 0 then
      .error .overflow
    else
      .ok (_s, 0)
  else if cancelWithdrawContextValid = 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let side0 := orders.values[0]!.side.toUInt64
    let side1ok :=
      orders.length ≤ 1 ||
        orders.values[1]!.side.toUInt64 = 0 ||
        orders.values[1]!.side.toUInt64 = 1
    let side2ok :=
      orders.length ≤ 2 ||
        orders.values[2]!.side.toUInt64 = 0 ||
        orders.values[2]!.side.toUInt64 = 1
    let side3ok :=
      orders.length ≤ 3 ||
        orders.values[3]!.side.toUInt64 = 0 ||
        orders.values[3]!.side.toUInt64 = 1
    let side4ok :=
      orders.length ≤ 4 ||
        orders.values[4]!.side.toUInt64 = 0 ||
        orders.values[4]!.side.toUInt64 = 1
    let side5ok :=
      orders.length ≤ 5 ||
        orders.values[5]!.side.toUInt64 = 0 ||
        orders.values[5]!.side.toUInt64 = 1
    let side6ok :=
      orders.length ≤ 6 ||
        orders.values[6]!.side.toUInt64 = 0 ||
        orders.values[6]!.side.toUInt64 = 1
    let side7ok :=
      orders.length ≤ 7 ||
        orders.values[7]!.side.toUInt64 = 0 ||
        orders.values[7]!.side.toUInt64 = 1
    if (side0 ≠ 0 && side0 ≠ 1) || !side1ok || !side2ok || !side3ok || !side4ok || !side5ok ||
        !side6ok || !side7ok then
      .error .overflow
    else
      let layout := Examples.Svm.PhoenixV1.small 2
      let traderKey0 := signerKey 3
      let traderIndex := layout.findTrader
        traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
      let marketSequence := layout.marketSequence
      let _ := layout.setMarketSequence (marketSequence + 1)
      let _ := beginMarketBatchAt 10 2 2 marketSequence
      let o0 := orders.values[0]!
      let released0 ←
        cancelOneReleased512At layout traderKey0 traderIndex side0 o0.price o0.sequence
      let quote0 ← addReleasedAcc512At 0 side0 released0 1
      let base0 ← addReleasedAcc512At 0 side0 released0 0
      if orders.length ≥ 2 then
        let o1 := orders.values[1]!
        let side1 := o1.side.toUInt64
        let released1 ←
          cancelOneReleased512At layout traderKey0 traderIndex side1 o1.price o1.sequence
        let quote01 ← addReleasedAcc512At quote0 side1 released1 1
        let base01 ← addReleasedAcc512At base0 side1 released1 0
        if orders.length ≥ 3 then
          let o2 := orders.values[2]!
          let side2 := o2.side.toUInt64
          let released2 ←
            cancelOneReleased512At layout traderKey0 traderIndex side2 o2.price o2.sequence
          let quote012 ← addReleasedAcc512At quote01 side2 released2 1
          let base012 ← addReleasedAcc512At base01 side2 released2 0
          if orders.length ≥ 4 then
            let o3 := orders.values[3]!
            let side3 := o3.side.toUInt64
            let released3 ←
              cancelOneReleased512At layout traderKey0 traderIndex side3 o3.price o3.sequence
            let quote0123 ← addReleasedAcc512At quote012 side3 released3 1
            let base0123 ← addReleasedAcc512At base012 side3 released3 0
            if orders.length ≥ 5 then
              let o4 := orders.values[4]!
              let side4 := o4.side.toUInt64
              let released4 ←
                cancelOneReleased512At layout traderKey0 traderIndex side4 o4.price o4.sequence
              let quote01234 ← addReleasedAcc512At quote0123 side4 released4 1
              let base01234 ← addReleasedAcc512At base0123 side4 released4 0
              if orders.length ≥ 6 then
                let o5 := orders.values[5]!
                let side5 := o5.side.toUInt64
                let released5 ←
                  cancelOneReleased512At layout traderKey0 traderIndex side5 o5.price o5.sequence
                let quote012345 ← addReleasedAcc512At quote01234 side5 released5 1
                let base012345 ← addReleasedAcc512At base01234 side5 released5 0
                if orders.length ≥ 7 then
                  let o6 := orders.values[6]!
                  let side6 := o6.side.toUInt64
                  let released6 ←
                    cancelOneReleased512At layout traderKey0 traderIndex side6 o6.price o6.sequence
                  let quote0123456 ← addReleasedAcc512At quote012345 side6 released6 1
                  let base0123456 ← addReleasedAcc512At base012345 side6 released6 0
                  if orders.length ≥ 8 then
                    let o7 := orders.values[7]!
                    let side7 := o7.side.toUInt64
                    let released7 ←
                      cancelOneReleased512At layout traderKey0 traderIndex side7 o7.price o7.sequence
                    let quoteAll ← addReleasedAcc512At quote0123456 side7 released7 1
                    let baseAll ← addReleasedAcc512At base0123456 side7 released7 0
                    let _ ←
                      finishCancelMultipleWithdraw512At layout traderIndex quoteAll baseAll
                    .ok (_s, 0)
                  else
                    let _ ←
                      finishCancelMultipleWithdraw512At layout traderIndex quote0123456 base0123456
                    .ok (_s, 0)
                else
                  let _ ←
                    finishCancelMultipleWithdraw512At layout traderIndex quote012345 base012345
                  .ok (_s, 0)
              else
                let _ ←
                  finishCancelMultipleWithdraw512At layout traderIndex quote01234 base01234
                .ok (_s, 0)
            else
              let _ ←
                finishCancelMultipleWithdraw512At layout traderIndex quote0123 base0123
              .ok (_s, 0)
          else
            let _ ←
              finishCancelMultipleWithdraw512At layout traderIndex quote012 base012
            .ok (_s, 0)
        else
          let _ ←
            finishCancelMultipleWithdraw512At layout traderIndex quote01 base01
          .ok (_s, 0)
      else
        let _ ←
          finishCancelMultipleWithdraw512At layout traderIndex quote0 base0
        .ok (_s, 0)

/--
Official Phoenix `WithdrawFunds` tag 12 wire (exact-lots slice):
`0c || quote_lots:u64 || base_lots:u64`. Zero lots skip that side. Reuses the shared nine-account
classic Token withdraw context and claims from free balances before vault CPI. Missing trader or
insufficient free lots fail closed. Zero/zero is a header-only sequence bump.
-/
@[pf_entry, pf_svm_raw 12 9 0]
def withdrawFunds (_s : State) (quoteLots baseLots : UInt64) :
    Except Error (State × UInt64) := do
  if cancelWithdrawContextValid = 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let layout := Examples.Svm.PhoenixV1.small 2
    let traderKey0 := signerKey 3
    let traderIndex := layout.findTrader
      traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
    if traderIndex = 0 then
      .error .overflow
    else
      let marketSequence := layout.marketSequence
      let _ := layout.setMarketSequence (marketSequence + 1)
      let _ := beginMarketBatchAt 12 2 2 marketSequence
      if quoteLots = 0 && baseLots = 0 then
        let _ := finishMarketBatch
        .ok (_s, 0)
      else
        let quoteLotSize := layout.quoteLotSize
        let baseLotSize := layout.baseLotSize
        let quoteDivisor := if quoteLots = 0 then 1 else quoteLots
        let baseDivisor := if baseLots = 0 then 1 else baseLots
        if quoteLotSize ≤ u64Max / quoteDivisor && baseLotSize ≤ u64Max / baseDivisor then
          let quoteAtoms := quoteLots * quoteLotSize
          let baseAtoms := baseLots * baseLotSize
          let _ ←
            if quoteLots = 0 then .ok 0
            else claimReleasedFunds512At layout traderIndex 0 quoteLots
          let _ ←
            if baseLots = 0 then .ok 0
            else claimReleasedFunds512At layout traderIndex 1 baseLots
          let _ := withdrawReleasedAt 0 quoteAtoms
          let _ := withdrawReleasedAt 1 baseAtoms
          let _ := finishMarketBatch
          .ok (_s, 0)
        else
          .error .overflow

/-- Credit free lots for DepositFunds. Overflow of free + lots fails closed. -/
def creditFreeFunds512At (layout : Examples.Svm.PhoenixV1.Layout)
    (traderIndex side lots : UInt64) : Except Error UInt64 :=
  if side = 0 then
    let free := layout.quoteFree traderIndex
    if free ≤ u64Max - lots then
      let _ := layout.setQuoteFree traderIndex (free + lots)
      .ok lots
    else
      .error .overflow
  else
    let free := layout.baseFree traderIndex
    if free ≤ u64Max - lots then
      let _ := layout.setBaseFree traderIndex (free + lots)
      .ok lots
    else
      .error .overflow

/-- Trader → vault classic Token transfer geometry for DepositFunds (tag 13). -/
@[pf_inline] def quoteDepositTokenAccounts :
    ProofForge.Svm.Sdk.Token.UncheckedTransferAccounts :=
  .at 7 4 6 2

@[pf_inline] def baseDepositTokenAccounts :
    ProofForge.Svm.Sdk.Token.UncheckedTransferAccounts :=
  .at 7 3 5 2

/-- Pull atoms from the trader token account into the market vault. Trader is the ordinary signer. -/
def depositAtomsAt (side atoms : UInt64) : UInt64 :=
  if atoms = 0 then
    0
  else if side = 0 then
    ProofForge.Svm.Sdk.Token.transferWith quoteDepositTokenAccounts atoms
  else
    ProofForge.Svm.Sdk.Token.transferWith baseDepositTokenAccounts atoms

/--
Official Phoenix `DepositFunds` tag 13 wire (exact-lots slice):
`0d || quote_lots:u64 || base_lots:u64`. Zero lots skip that side. Reuses the shared nine-account
classic Token context; trader signer transfers into vaults then free balances are credited.
Missing trader or free-balance overflow fails closed. Zero/zero is a header-only sequence bump.
-/
@[pf_entry, pf_svm_raw 13 9 0]
def depositFunds (_s : State) (quoteLots baseLots : UInt64) :
    Except Error (State × UInt64) := do
  if cancelWithdrawContextValid = 0 || cancelAllStorageValid512At 2 = 0 then
    .error .overflow
  else
    let layout := Examples.Svm.PhoenixV1.small 2
    let traderKey0 := signerKey 3
    let traderIndex := layout.findTrader
      traderKey0 (accKeyWord 3 1) (accKeyWord 3 2) (accKeyWord 3 3)
    if traderIndex = 0 then
      .error .overflow
    else
      let marketSequence := layout.marketSequence
      let _ := layout.setMarketSequence (marketSequence + 1)
      let _ := beginMarketBatchAt 13 2 2 marketSequence
      if quoteLots = 0 && baseLots = 0 then
        let _ := finishMarketBatch
        .ok (_s, 0)
      else
        let quoteLotSize := layout.quoteLotSize
        let baseLotSize := layout.baseLotSize
        let quoteDivisor := if quoteLots = 0 then 1 else quoteLots
        let baseDivisor := if baseLots = 0 then 1 else baseLots
        if quoteLotSize ≤ u64Max / quoteDivisor && baseLotSize ≤ u64Max / baseDivisor then
          let quoteAtoms := quoteLots * quoteLotSize
          let baseAtoms := baseLots * baseLotSize
          let _ := depositAtomsAt 0 quoteAtoms
          let _ := depositAtomsAt 1 baseAtoms
          let _ ←
            if quoteLots = 0 then .ok 0
            else creditFreeFunds512At layout traderIndex 0 quoteLots
          let _ ←
            if baseLots = 0 then .ok 0
            else creditFreeFunds512At layout traderIndex 1 baseLots
          let _ := finishMarketBatch
          .ok (_s, 0)
        else
          .error .overflow


/-- Direct boundary probe used to prove a short account fails before reading bytes 32..39. -/
@[pf_entry]
def headerSeats (_s : State) : UInt64 :=
  accDataWord 1 4

attribute [pf_inline] accountBytesFor boundedBodyEntryCount lowUInt32 highUInt32 packUInt32
  key4Before key4Equal reduceStatusValidAt
  thirdRoot thirdNode1Links thirdNode1ParentColor thirdNode2Links
  thirdNode2ParentColor thirdNode3Links thirdNode3ParentColor
  allocatorHeaderValid threeAllocatorHeadersValid nodeIndexOrNullValid boundedBidRootPrice
  boundedNodeSlot bidKeyBefore boundedBidChildValid boundedBidRootNeighborhoodValid
  bidRootNeighborhood512 bidRootNeighborhood1024 bidRootNeighborhood2048
  bidRootNeighborhood4096 profileAccountBytesAt profileAccountBytes allocatorHeadersValidAt
  allocatorHeadersValid reduceAskFreeFunds512At reduceBidFreeFunds512At reduceFreeFunds512At
  quoteLotsReleased512At claimReleasedFunds512At beginMarketBatchAt recordReduceAt recordPlaceAt
  recordFillAt recordFillSummaryAt adjustedQuoteLots512At takerFeeQuoteLotsOf takerFeeQuoteLots512At
  postingQuoteLotsOrZero512At twoMatchPostingValid512At
  finishMarketBatch withdrawReleasedAt cancelAllStorageValid512At cancelAllTraderIndex512At
  beginCancelAll cancelAllBids512At cancelAllAsks512At cancelUpToBids512At
  cancelUpToAsks512At finishCancelAll
  cancelWithdrawContextValid placeFreeFundsContextValid placePostOnlyFreeFunds512At
  placeLimitOneMatchFreeFunds512At placeLimitTwoMatchesFreeFunds512At
  cancelOneByIdFreeFunds512At releasedLotsForCancel512At
  cancelOneReleased512At
  finishCancelMultipleWithdraw512At
  addReleasedAcc512At
  creditFreeFunds512At depositAtomsAt

end Examples.Svm.PhoenixV1Profile