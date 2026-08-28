import ProofForge.Svm.Sdk.Account
import ProofForge.Svm.Sdk.Program

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

/-! ## Allocation-free packed state views -/

/-- Which official SPL Token program owns an exact base-state account. -/
inductive Flavor where
  | classic
  | token2022
  deriving BEq, Repr, Inhabited

@[pf_inline] def Flavor.programId : Flavor → Program.Id
  | .classic => Program.classicToken
  | .token2022 => Program.token2022

@[pf_inline] def Flavor.owns
    (flavor : Flavor) (program account : Account.Handle) : Bool :=
  match flavor with
  | .classic => Program.classicToken.owns program account
  | .token2022 => Program.token2022.owns program account

/--
Zero-copy view of one exact 165-byte SPL Token Account plus its executable Token program account.
The descriptor contains only compile-time account handles and a program flavor. Token-2022
extension-bearing accounts deliberately do not pass this exact base view; they require the bounded
TLV policy owned by `Svm.Cpi.TokenTlv`.
-/
structure AccountState where
  account : Account.Handle
  tokenProgram : Account.Handle
  flavor : Flavor
  deriving BEq, Repr, Inhabited

attribute [pf_inline] AccountState.account AccountState.tokenProgram AccountState.flavor

@[pf_inline] def AccountState.classic
    (account tokenProgram : Account.Handle) : AccountState :=
  { account, tokenProgram, flavor := .classic }

@[pf_inline] def AccountState.token2022
    (account tokenProgram : Account.Handle) : AccountState :=
  { account, tokenProgram, flavor := .token2022 }

def AccountState.wellFormed (view : AccountState) (accountLimit : Nat := 64) : Bool :=
  view.account.wellFormed accountLimit && view.tokenProgram.wellFormed accountLimit

/-- Packed `Account.state` byte at absolute offset 108. -/
@[pf_inline] def AccountState.state (view : AccountState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ => (account.dataWord 13 >>> 32) &&& 0xff

/-- Complete fixed-layout/owner/program/state-enum validation. -/
@[pf_inline] def AccountState.packedValid (view : AccountState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let state := (account.dataWord 13 >>> 32) &&& 0xff
      account.dataLen = 165 && flavor.owns tokenProgram account && state ≤ 2

/-- Official `IsInitialized`: both Initialized and Frozen are initialized states. -/
@[pf_inline] def AccountState.isInitialized (view : AccountState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let state := (account.dataWord 13 >>> 32) &&& 0xff
      account.dataLen = 165 && flavor.owns tokenProgram account &&
        (state = 1 || state = 2)

/-- True only for the ordinary Initialized state, not Frozen. -/
@[pf_inline] def AccountState.isUsable (view : AccountState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let state := (account.dataWord 13 >>> 32) &&& 0xff
      account.dataLen = 165 && flavor.owns tokenProgram account && state = 1

@[pf_inline] def AccountState.isFrozen (view : AccountState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let state := (account.dataWord 13 >>> 32) &&& 0xff
      account.dataLen = 165 && flavor.owns tokenProgram account && state = 2

/-- Packed `Account.amount` at absolute offset 64. -/
@[pf_inline] def AccountState.amount (view : AccountState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ => account.dataWord 8

/-- Compare the packed 32-byte mint field at offset 0 with a selected mint account key. -/
@[pf_inline] def AccountState.mintIs
    (view : AccountState) (mint : Account.Handle) : Bool :=
  match view with
  | ⟨account, _, _⟩ =>
      account.dataWord 0 = mint.keyWord 0 && account.dataWord 1 = mint.keyWord 1 &&
        account.dataWord 2 = mint.keyWord 2 && account.dataWord 3 = mint.keyWord 3

/-- Compare the packed 32-byte authority/owner field at offset 32 with an account key. -/
@[pf_inline] def AccountState.authorityIs
    (view : AccountState) (authority : Account.Handle) : Bool :=
  match view with
  | ⟨account, _, _⟩ =>
      account.dataWord 4 = authority.keyWord 0 &&
        account.dataWord 5 = authority.keyWord 1 &&
        account.dataWord 6 = authority.keyWord 2 &&
        account.dataWord 7 = authority.keyWord 3

/-- Zero-copy view of one exact 82-byte SPL Mint plus its executable Token program account. -/
structure MintState where
  account : Account.Handle
  tokenProgram : Account.Handle
  flavor : Flavor
  deriving BEq, Repr, Inhabited

attribute [pf_inline] MintState.account MintState.tokenProgram MintState.flavor

@[pf_inline] def MintState.classic
    (account tokenProgram : Account.Handle) : MintState :=
  { account, tokenProgram, flavor := .classic }

@[pf_inline] def MintState.token2022
    (account tokenProgram : Account.Handle) : MintState :=
  { account, tokenProgram, flavor := .token2022 }

def MintState.wellFormed (view : MintState) (accountLimit : Nat := 64) : Bool :=
  view.account.wellFormed accountLimit && view.tokenProgram.wellFormed accountLimit

/-- Four-byte `COption<Pubkey>` tag at offset 0. -/
@[pf_inline] def MintState.mintAuthorityTag (view : MintState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ => account.dataWord 0 &&& 0xffffffff

/-- Reconstruct the unaligned little-endian supply at bytes 36..43. -/
@[pf_inline] def MintState.supply (view : MintState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ =>
      (account.dataWord 4 >>> 32) ||| ((account.dataWord 5 &&& 0xffffffff) <<< 32)

@[pf_inline] def MintState.decimals (view : MintState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ => (account.dataWord 5 >>> 32) &&& 0xff

@[pf_inline] def MintState.initializedByte (view : MintState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ => (account.dataWord 5 >>> 40) &&& 0xff

/-- Four-byte `COption<Pubkey>` tag at bytes 46..49. -/
@[pf_inline] def MintState.freezeAuthorityTag (view : MintState) : UInt64 :=
  match view with
  | ⟨account, _, _⟩ =>
      (account.dataWord 5 >>> 48) ||| ((account.dataWord 6 &&& 0xffff) <<< 16)

/-- Exact base length, authenticated owner/program, valid COption tags, and canonical bool byte. -/
@[pf_inline] def MintState.packedValid (view : MintState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let authorityTag := account.dataWord 0 &&& 0xffffffff
      let initialized := (account.dataWord 5 >>> 40) &&& 0xff
      let freezeTag :=
        (account.dataWord 5 >>> 48) ||| ((account.dataWord 6 &&& 0xffff) <<< 16)
      account.dataLen = 82 && flavor.owns tokenProgram account &&
        authorityTag ≤ 1 && freezeTag ≤ 1 && initialized ≤ 1

@[pf_inline] def MintState.isInitialized (view : MintState) : Bool :=
  match view with
  | ⟨account, tokenProgram, flavor⟩ =>
      let authorityTag := account.dataWord 0 &&& 0xffffffff
      let initialized := (account.dataWord 5 >>> 40) &&& 0xff
      let freezeTag :=
        (account.dataWord 5 >>> 48) ||| ((account.dataWord 6 &&& 0xffff) <<< 16)
      account.dataLen = 82 && flavor.owns tokenProgram account &&
        authorityTag ≤ 1 && freezeTag ≤ 1 && initialized = 1

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


/-- CheckedTransfer 的 5 个角色索引 wellFormed 分量提取。 -/
theorem checkedTransfer_wf_parts (accounts : CheckedTransferAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.tokenProgram.wellFormed L ∧
    accounts.source.wellFormed L ∧
    accounts.mint.wellFormed L ∧
    accounts.destination.wellFormed L ∧
    accounts.authority.wellFormed L := by
  simp only [CheckedTransferAccounts.wellFormed, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- UncheckedTransfer 的 4 个角色索引 wellFormed 分量提取。 -/
theorem uncheckedTransfer_wf_parts (accounts : UncheckedTransferAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.tokenProgram.wellFormed L ∧
    accounts.source.wellFormed L ∧
    accounts.destination.wellFormed L ∧
    accounts.authority.wellFormed L := by
  simp only [UncheckedTransferAccounts.wellFormed, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩


/-- CheckedTransfer 的 5 角色索引逐一有界（Nat 级推论）。 -/
theorem checkedTransfer_wf_bounds (accounts : CheckedTransferAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.tokenProgram.index < L ∧ accounts.source.index < L ∧
    accounts.mint.index < L ∧ accounts.destination.index < L ∧
    accounts.authority.index < L := by
  have hs := checkedTransfer_wf_parts accounts L h
  simp only [ProofForge.Svm.Sdk.CpiAccount.Handle.wellFormed, decide_eq_true_eq] at hs
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · constructor
        · omega
        · omega

/-- UncheckedTransfer 的 4 角色索引逐一有界。 -/
theorem uncheckedTransfer_wf_bounds (accounts : UncheckedTransferAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.tokenProgram.index < L ∧ accounts.source.index < L ∧
    accounts.destination.index < L ∧ accounts.authority.index < L := by
  have hs := uncheckedTransfer_wf_parts accounts L h
  simp only [ProofForge.Svm.Sdk.CpiAccount.Handle.wellFormed, decide_eq_true_eq] at hs
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · omega

end ProofForge.Svm.Sdk.Token



