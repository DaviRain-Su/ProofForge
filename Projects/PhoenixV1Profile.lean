import ProofForge

/-!
Phoenix v1 market-account profile gate.

The official program does not accept arbitrary runtime capacities. Its 24-byte `MarketSizeParams`
header selects one of twelve statically compiled `FIFOMarket<Pubkey, B, A, S>` layouts. This module
keeps the body opaque and validates only that dispatch boundary: canonical owner/discriminant,
whitelisted capacities, and the exact account length derived from the pinned Sokoban 0.3.0 layout.

This is deliberately a separate verifier program whose ProofForge state is account 0 and candidate
Phoenix market is account 1. It does not claim to execute the official market body.
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

/-- Direct boundary probe used to prove a short account fails before reading bytes 32..39. -/
@[pf_entry]
def headerSeats (_s : State) : UInt64 :=
  accDataWord 1 4

attribute [pf_inline] accountBytesFor

end Projects.PhoenixV1Profile
