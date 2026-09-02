import ProofForge

/-!
Independent consumer for the first-class SVM SDK `Pubkey` value. Physical account 0 is
ProofForge state; 1 is the authority under authentication; 2 is a peer account compared against
the authority; 3 is the program account whose complete key authenticates owners. All geometry is
compile-time static. Fixed keys and projected account keys/owners are compiler data: `pf_inline`
consumers erase every `Pubkey` to the four existing account key/owner word queries. There is no base58 decoder, byte buffer, heap allocation, pointer,
runtime account index, or word-level magic at any application site below.

Loader-v3 note: two positions naming the same key are duplicate aliases of one account. The
walked ABI rejects duplicates before any method body runs, so `keysEqual`/`peerKeyAccepted`
observe `0` for distinct keys and fail closed on equal keys; the positive complete-key equality
outcome is pinned by host guards and by the fixed-key/owner-vs-key views.
-/

namespace Examples.Svm.PubkeyGate
open ProofForge.Svm.Sdk

structure State where
  accepted : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Fixed authority account under authentication: physical account 1. -/
@[pf_inline] def authority : Account.Handle := Account.Handle.at 1

/-- Peer account compared against the authority: physical account 2. -/
@[pf_inline] def peer : Account.Handle := Account.Handle.at 2

/-- Program account whose key authenticates owners: physical account 3. -/
@[pf_inline] def programAccount : Account.Handle := Account.Handle.at 3

/-- Fixed 32-byte authority key (`SHA-256("pubkey-gate-authority")`, four little-endian words).
This is compiler data compared against account bytes in place; it is never decoded on chain. -/
@[pf_inline] def expectedAuthority : Pubkey :=
  Pubkey.ofWords 4363037911745304074 7049941761903427640
    2783927094010722786 9388334143586028085

/-- Fixed 32-byte expected owner (`SHA-256("pubkey-gate-owner")`). -/
@[pf_inline] def expectedOwner : Pubkey :=
  Pubkey.ofWords 9206327822447524757 5745585139120232019
    2488220196562544179 11478135293500621328

/--
One canonical authentication policy reused by every entry: project the account's complete key
once as a `Pubkey` value and compare values. Callers pass fixed keys, runtime-supplied keys, and
keys projected from other accounts through the same ordinary Lean function.
-/
@[pf_inline] def grants (expected : Pubkey) (account : Account.Handle) : Bool :=
  account.key.equals expected

@[pf_entry]
def init (initial : UInt64) : State :=
  { accepted := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.accepted

/-- The authority account carries exactly the fixed key. -/
@[pf_entry]
def authorityMatches (_s : State) : UInt64 :=
  if grants expectedAuthority authority then 1 else 0

/--
A runtime-supplied key arrives as four scalar entry words, is constructed once as a `Pubkey`
value in ordinary Lean source, and flows through the same `grants` policy.
-/
@[pf_entry]
def suppliedMatches (_s : State) (w0 w1 w2 w3 : UInt64) : UInt64 :=
  let supplied := Pubkey.ofWords w0 w1 w2 w3
  if grants supplied authority then 1 else 0

/-- The peer's complete key, passed as a value, is accepted by the same policy. -/
@[pf_entry]
def peerKeyAccepted (_s : State) : UInt64 :=
  if grants peer.key authority then 1 else 0

/-- Complete-key equality between two statically selected accounts. -/
@[pf_entry]
def keysEqual (_s : State) : UInt64 :=
  if authority.sameKey peer then 1 else 0

/-- Complete-key inequality between the authority and the fixed expected key. -/
@[pf_entry]
def keyDiffers (_s : State) : UInt64 :=
  if authority.key.notEquals expectedAuthority then 1 else 0

/-- The authority's complete owner equals the peer's complete key. -/
@[pf_entry]
def ownerIsPeerKey (_s : State) : UInt64 :=
  if authority.ownerIsKeyOf peer then 1 else 0

/-- The authority's complete owner equals the fixed expected owner. -/
@[pf_entry]
def ownerMatches (_s : State) : UInt64 :=
  if authority.owner.equals expectedOwner then 1 else 0

/-- The program account is executable, carries the fixed expected owner key, and owns the
authority account: canonical matching across key and owner projections. -/
@[pf_entry]
def ownerAuthenticated (_s : State) : UInt64 :=
  if programAccount.isExecutable = 1 &&
      expectedOwner.matchesKey programAccount &&
      authority.ownerIsKeyOf programAccount then 1 else 0

/--
Gated mutation: only the exact 32-byte authority key is accepted. A mismatch in any of the four
words fails closed with `Custom(4097)` and leaves the committed state byte-identical.
-/
@[pf_entry]
def accept (s : State) : Except Error (State × UInt64) :=
  if grants expectedAuthority authority then
    let next := s.accepted + 1
    .ok ({ accepted := next }, next)
  else
    .error .unauthorized

end Examples.Svm.PubkeyGate