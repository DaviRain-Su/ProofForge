import ProofForge.Svm.Sdk.Account

/-!
# SVM SDK classic SPL Token facade

Stable source names for the existing fixed-account classic SPL Token Runtime wrappers. Every
function is `pf_inline` and delegates to one Runtime wrapper; the extractor unfolds these
facades into the same generic invoke contract, so no Ops, IR, Emit, Extract, or Component
behavior changes.

Geometry is the honest fixed-account classic Token shape already pinned by `Svm.Runtime`:

- external account 0 is the signing authority/owner (or payer), unless the wrapper documents
  otherwise;
- remaining external accounts follow each official instruction's account order;
- the Token program is the CPI callee at the documented external index;
- `decimals` and static instruction indexes must reduce to extraction-time constants, while
  `amount`, lamports-like scalars, and seed groups are ordinary instruction values.

Role-named transfer descriptors distinguish CPI-relative handles from physical account handles
and erase to the existing indexed Runtime wrappers. Dynamic account tables, runtime-selected
geometry, alternate program ids, and Token-2022 extension semantics remain fail closed.
-/

namespace ProofForge.Svm.Sdk.Token

/-- Role-named classic Token `TransferChecked` account geometry. Every handle is relative to the
external-account region after state, exactly like Runtime CPI metas and `PdaSeed.accKey`; the
descriptor is compile-time data and is erased during extraction. -/
structure CheckedTransferAccounts where
  tokenProgram : CpiAccount.Handle
  source : CpiAccount.Handle
  mint : CpiAccount.Handle
  destination : CpiAccount.Handle
  authority : CpiAccount.Handle
  deriving BEq, Repr, Inhabited

attribute [pf_inline]
  CheckedTransferAccounts.tokenProgram CheckedTransferAccounts.source
  CheckedTransferAccounts.mint CheckedTransferAccounts.destination
  CheckedTransferAccounts.authority

@[pf_inline] def CheckedTransferAccounts.at
    (tokenProgram source mint destination authority : Nat) : CheckedTransferAccounts :=
  { tokenProgram := .at tokenProgram
    source := .at source
    mint := .at mint
    destination := .at destination
    authority := .at authority }

def CheckedTransferAccounts.wellFormed
    (accounts : CheckedTransferAccounts) (accountLimit : Nat := 64) : Bool :=
  accounts.tokenProgram.wellFormed accountLimit &&
    accounts.source.wellFormed accountLimit &&
    accounts.mint.wellFormed accountLimit &&
    accounts.destination.wellFormed accountLimit &&
    accounts.authority.wellFormed accountLimit

/-- Role-named classic unchecked `Transfer` geometry for protocols that authenticate the mint in
their own account header. Prefer `CheckedTransferAccounts` for ordinary token movement. -/
structure UncheckedTransferAccounts where
  tokenProgram : CpiAccount.Handle
  source : CpiAccount.Handle
  destination : CpiAccount.Handle
  authority : CpiAccount.Handle
  deriving BEq, Repr, Inhabited

attribute [pf_inline]
  UncheckedTransferAccounts.tokenProgram UncheckedTransferAccounts.source
  UncheckedTransferAccounts.destination UncheckedTransferAccounts.authority

@[pf_inline] def UncheckedTransferAccounts.at
    (tokenProgram source destination authority : Nat) : UncheckedTransferAccounts :=
  { tokenProgram := .at tokenProgram
    source := .at source
    destination := .at destination
    authority := .at authority }

def UncheckedTransferAccounts.wellFormed
    (accounts : UncheckedTransferAccounts) (accountLimit : Nat := 64) : Bool :=
  accounts.tokenProgram.wellFormed accountLimit &&
    accounts.source.wellFormed accountLimit &&
    accounts.destination.wellFormed accountLimit &&
    accounts.authority.wellFormed accountLimit

/-- Closed classic Token `TransferChecked`: external account 0 is the signing authority;
source is account 1 (writable), mint account 2 (read-only), destination account 3 (writable).
`decimals` must reduce to an extraction-time constant; `amount` may be a dynamic scalar. -/
@[pf_inline] def transferChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenTransferChecked amount decimals

/-- Execute a statically described `TransferChecked` with an ordinary transaction signer. -/
@[pf_inline] def transferCheckedWith
    (accounts : CheckedTransferAccounts) (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenTransferCheckedIx
    (UInt64.ofNat accounts.tokenProgram.index)
    (UInt64.ofNat accounts.source.index)
    (UInt64.ofNat accounts.mint.index)
    (UInt64.ofNat accounts.destination.index)
    (UInt64.ofNat accounts.authority.index)
    amount decimals

/-- Statically indexed classic Token `TransferChecked` whose authority is a PDA signer group.
`seeds` is compile-time-shaped and does not include the final bump; the bump is an ordinary
instruction value produced by PDA discovery. -/
@[pf_inline] def transferCheckedSignedWith
    (accounts : CheckedTransferAccounts) (amount decimals : UInt64)
    (seeds : Array ProofForge.Svm.Runtime.PdaSeed) (bump : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenTransferCheckedSignedIx
    (UInt64.ofNat accounts.tokenProgram.index)
    (UInt64.ofNat accounts.source.index)
    (UInt64.ofNat accounts.mint.index)
    (UInt64.ofNat accounts.destination.index)
    (UInt64.ofNat accounts.authority.index)
    amount decimals seeds bump

/-- Statically indexed unchecked classic Token `Transfer` (tag 3) whose authority is a PDA
signer group. Metas are source / destination / authority; no mint account or decimals byte. -/
@[pf_inline] def transferSignedWith
    (accounts : UncheckedTransferAccounts) (amount : UInt64)
    (seeds : Array ProofForge.Svm.Runtime.PdaSeed) (bump : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenTransferSignedIx
    (UInt64.ofNat accounts.tokenProgram.index)
    (UInt64.ofNat accounts.source.index)
    (UInt64.ofNat accounts.destination.index)
    (UInt64.ofNat accounts.authority.index)
    amount seeds bump

/-- Closed classic Token `MintToChecked`: external account 0 is the signing mint authority;
mint is account 1 (writable), destination account 2 (writable). `decimals` must reduce to an
extraction-time constant. -/
@[pf_inline] def mintToChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenMintToChecked amount decimals

/-- Closed classic Token `BurnChecked`: external account 0 is the signing token owner; source
is account 1 (writable), mint account 2 (writable). `decimals` must reduce to an
extraction-time constant. -/
@[pf_inline] def burnChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenBurnChecked amount decimals

/-- Closed classic Token `InitializeAccount3`: external account 0 is the new account owner;
account is account 1 (writable), mint account 2 (read-only). -/
@[pf_inline] def initializeAccount : UInt64 :=
  ProofForge.Svm.Runtime.tokenInitAccount

/-- Closed classic Token `InitializeMint2`: decimals are pinned to 6, mint authority is
external account 0, and freeze authority is unset; mint is account 1 (writable). -/
@[pf_inline] def initializeMint6 : UInt64 :=
  ProofForge.Svm.Runtime.tokenInitMint

/-- Closed classic Token `CloseAccount`: external account 0 is the signing owner; source is
account 1 (writable) and the lamport recipient is account 2 (writable). -/
@[pf_inline] def closeAccount : UInt64 :=
  ProofForge.Svm.Runtime.tokenCloseAccount

/-- Closed unchecked classic Token `Approve` (tag 4): external account 0 is the signing owner;
source is account 1 (writable), delegate account 2 (read-only). No decimals enter the data. -/
@[pf_inline] def approve (amount : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenApprove amount

/-- Closed classic Token `ApproveChecked`: external account 0 is the signing owner; source is
account 1 (writable), mint account 2 (read-only), delegate account 3 (read-only). `decimals`
must reduce to an extraction-time constant. -/
@[pf_inline] def approveChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenApproveChecked amount decimals

/-- Closed classic Token `Revoke`: external account 0 is the signing owner; source is
account 1 (writable). Clears the source delegate. -/
@[pf_inline] def revoke : UInt64 :=
  ProofForge.Svm.Runtime.tokenRevoke

/-- Closed classic Token `FreezeAccount`: external account 0 is the signing freeze authority;
account is account 1 (writable), mint account 2 (read-only). -/
@[pf_inline] def freezeAccount : UInt64 :=
  ProofForge.Svm.Runtime.tokenFreezeAccount

/-- Closed classic Token `ThawAccount`: same fixed account geometry as `freezeAccount`. -/
@[pf_inline] def thawAccount : UInt64 :=
  ProofForge.Svm.Runtime.tokenThawAccount

/-- Closed classic Token `SetAuthority` for `MintTokens`: external account 0 is the signing
current mint authority, mint is account 1 (writable), and the new authority is the public key
of external account 2. -/
@[pf_inline] def setMintAuthority : UInt64 :=
  ProofForge.Svm.Runtime.tokenSetMintAuthority

/-- Closed classic Token `SetAuthority` for `AccountOwner`: external account 0 is the signing
current owner, account is account 1 (writable), and the new owner is the public key of
external account 2. -/
@[pf_inline] def setAccountAuthority : UInt64 :=
  ProofForge.Svm.Runtime.tokenSetAccountAuthority

/-- Closed classic Token `SyncNative`: account 1 is the writable native token account whose
amount is refreshed from its underlying lamports. No owner signature is required. -/
@[pf_inline] def syncNative : UInt64 :=
  ProofForge.Svm.Runtime.tokenSyncNative

/-- Closed classic Token `InitializeMultisig2` (tag 19, no rent sysvar): this slice pins
`m = 2` with external accounts 2 and 3 as the two signers; the multisig is account 1
(writable). -/
@[pf_inline] def initializeMultisig2 : UInt64 :=
  ProofForge.Svm.Runtime.tokenInitMultisig

/-- Closed classic Token `GetAccountDataSize`: account 1 is the mint and the Token program is
external account 2. The returned value is the last CPI return word. -/
@[pf_inline] def baseAccountDataSize : UInt64 :=
  ProofForge.Svm.Runtime.tokenAccountSize

end ProofForge.Svm.Sdk.Token
