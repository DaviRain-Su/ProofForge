import ProofForge.Svm.Cpi.TokenTlv

namespace ProofForge.Svm.Runtime


/--
当前 slot。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.slot`（偏移 0）。这是物理 slot，不是逻辑 block。

宿主侧是不可约 stub：定理把它当未指定的 `UInt64`，不要unfold成 0。
其余 Clock 字段本剖面 fail closed。
-/
@[irreducible] def clockSlot : UInt64 := 0

/--
当前 epoch。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.epoch`（偏移 16）。宿主侧是不可约 stub。
`epoch_start_timestamp` 本剖面 fail closed。
-/
@[irreducible] def clockEpoch : UInt64 := 0

/--
Future epoch for which the leader schedule was most recently calculated. Extracted programs read
`Clock.leader_schedule_epoch` at native `repr(C)` offset 24. The host stub is irreducible.
-/
@[irreducible] def clockLeaderScheduleEpoch : UInt64 := 0

/--
当前 unix 时间戳。抽出后发射 `sol_get_clock_sysvar`，读
`Clock.unix_timestamp`（偏移 32）为无符号 `u64`。
宿主侧是不可约 stub。有符号语义本剖面不建模。
-/
@[irreducible] def unixTime : UInt64 := 0

/--
`dataLen` 字节账户的 rent-exempt 下限。
抽出后发射 `sol_get_rent_sysvar`，读 `lamports_per_byte`，再乘 `128 + dataLen`。
`dataLen` 必须在抽出时是常量。宿主侧是不可约 stub。
`exemption_threshold` 当浮点用仍 fail closed。
-/
@[irreducible] def rentExemption (dataLen : UInt64) : UInt64 :=
  let _ := dataLen
  0

/--
当前 `EpochSchedule.slots_per_epoch`。抽出后发射
`sol_get_epoch_schedule_sysvar`，读 native `repr(C)` 偏移 0。宿主侧是不可约 stub。
-/
@[irreducible] def slotsPerEpoch : UInt64 := 0

/-- Native `EpochSchedule.leader_schedule_slot_offset` at offset 8. -/
@[irreducible] def epochScheduleLeaderScheduleSlotOffset : UInt64 := 0

/-- Native `EpochSchedule.warmup` byte at offset 16, canonicalized by the SDK to `Bool`. -/
@[irreducible] def epochScheduleWarmup : UInt64 := 0

/-- Native `EpochSchedule.first_normal_epoch` at offset 24 after seven C-layout padding bytes. -/
@[irreducible] def epochScheduleFirstNormalEpoch : UInt64 := 0

/-- Native `EpochSchedule.first_normal_slot` at offset 32. -/
@[irreducible] def epochScheduleFirstNormalSlot : UInt64 := 0

/-! Allocation-free invocation telemetry. Host stubs intentionally return zero; extracted SVM
programs bind these leaves to the exact official syscall symbols through `Svm.Telemetry`. -/

/-- Remaining compute units at the instant this query executes. The query itself consumes units. -/
@[irreducible] def remainingComputeUnits : UInt64 := 0

/-- Current invocation stack height: transaction-level instructions are 1 and each CPI adds 1. -/
@[irreducible] def stackHeight : UInt64 := 0

/-- Emit the runtime's standard remaining-compute diagnostic. No numeric result is returned. -/
@[irreducible] def logComputeUnits : UInt64 := 0

/-- Emit five `UInt64` values through Solana's allocation-free hexadecimal numeric logger. -/
@[irreducible] def log64
    (first second third fourth fifth : UInt64) : UInt64 :=
  let _ := first
  let _ := second
  let _ := third
  let _ := fourth
  let _ := fifth
  0

/--
Reverse the eight bytes of one `u64`. The source body gives host evaluation its exact semantics;
the SVM extractor preserves the call as one value intrinsic and the emitter lowers it to sBPF
`be64`. This uses registers and fixed stack scratch only; it does not allocate heap memory.
-/
def svmByteSwap64 (word : UInt64) : UInt64 :=
  ((word &&& 0x00000000000000ff) <<< 56) |||
  ((word &&& 0x000000000000ff00) <<< 40) |||
  ((word &&& 0x0000000000ff0000) <<< 24) |||
  ((word &&& 0x00000000ff000000) <<< 8) |||
  ((word &&& 0x000000ff00000000) >>> 8) |||
  ((word &&& 0x0000ff0000000000) >>> 24) |||
  ((word &&& 0x00ff000000000000) >>> 40) |||
  ((word &&& 0xff00000000000000) >>> 56)

/--
账户 0 公钥的第一个小端 `u64`（`ACC0_KEY+0`）。
用到这个叶子的入口会检查 `is_signer`。

这是指定账户的 key，不是 `tx.origin`，也不是 fee payer。
完整 32 字节以后再开。
-/
@[irreducible] def signerKey0 : UInt64 := 0

/--
内层 AccountMeta。`acc` 是 state 账户之后的 CPI 账户区下标；编译期钉死下标和旗。
物理账户 0 永远留给已认证的 ProofForge state。
-/
structure CpiMeta where
  acc : UInt64
  signer : Bool := false
  writable : Bool := false
  /-- Reject the invocation before CPI unless this account has exactly this many data bytes. -/
  expectedDataLen : Option UInt64 := none
  /-- Typed account-data policy (e.g. the bounded Token-2022 TLV cursor); mutually exclusive
  with `expectedDataLen`. The policy's full meaning is owned by the target-side plan plus its
  sole interpreter, not by source code. -/
  accountData : Option Cpi.TokenTlv.Policy := none
  deriving Repr, DecidableEq, Inhabited

/-- 内层 instruction data 的一段。长度和布局编译期钉死。 -/
inductive CpiWord where
  | u8le (v : UInt64)
  | u16le (v : UInt64)
  | u32le (v : UInt64)
  | u64le (v : UInt64)
  /-- One-byte data prefix that also declares the matching signed raw self-entry. -/
  | selfEntry (tag : UInt64) (authoritySeed : String)
  | ascii (s : String)
  | programId
  | accKey (i : UInt64)
  deriving Repr, Inhabited

/--
One compile-time-shaped PDA seed. `stateKey` is physical account 0; `accKey i` and
`accData i offset length` are relative to the external-account region after state, matching
`CpiMeta.acc`. Account-data slices are bounded to Solana's 32-byte seed maximum and point directly
into the serialized account input; they do not allocate or copy persistent data. The final bump is
supplied separately so one representation serves both PDA discovery and signed CPI.
-/
inductive PdaSeed where
  | ascii (s : String)
  | stateKey
  | accKey (i : UInt64)
  | accData (i offset length : UInt64)
  deriving Repr, Inhabited

/--
编译期钉死的 CPI。抽出器认这个名字，发射 `sol_invoke_signed_c`。
`programIx`、metas 和 `.accKey` 都相对于 state 之后的 CPI 账户区，且必须在抽出时已知。
宿主侧是不可约 stub，返回 0，不要当链上结果用。
运行时拼 program id / remaining accounts / 变长 data 仍 fail closed。
-/
@[irreducible] def invoke (programIx : UInt64) (metas : Array CpiMeta) (data : Array CpiWord) :
    UInt64 :=
  let _ := programIx
  let _ := metas
  let _ := data
  0

/--
一组 signer seeds：一条 ASCII 种子 + 一个 bump。
抽出器认这个名字，发射带 `SolSignerSeeds` 的 `sol_invoke_signed_c`。
宿主侧是不可约 stub，返回 0。多组 seeds / 运行时拼种子 fail closed。
-/
@[irreducible] def invokeSigned (programIx : UInt64) (metas : Array CpiMeta)
    (data : Array CpiWord) (seed : String) (bump : UInt64) : UInt64 :=
  let _ := programIx
  let _ := metas
  let _ := data
  let _ := seed
  let _ := bump
  0

/--
One signer group with a compile-time-shaped list of PDA seeds plus a runtime bump. Seed count,
seed kinds, account indices, metas, and instruction layout must all be known during extraction.
This covers Solana authorities such as `["vault", market_key, mint_key, bump]` without teaching
the extractor or emitter about a particular Program.
-/
@[irreducible] def invokeSignedSeeds (programIx : UInt64) (metas : Array CpiMeta)
    (data : Array CpiWord) (seeds : Array PdaSeed) (bump : UInt64) : UInt64 :=
  let _ := programIx
  let _ := metas
  let _ := data
  let _ := seeds
  let _ := bump
  0

/--
Open a bounded invocation-local recorder. Static arguments describe the sink and byte geometry;
`header` excludes the one-byte raw self-entry tag, which the component prepends. Extraction lowers
this to a component call backed by Solana's 32 KiB downward bump allocator. No heap address is
observable in source code or persistent account data.
-/
@[irreducible] def batchRecorderBegin
    (logAccount selfEntryTag : UInt64) (authoritySeed : String)
    (maxBytes headerBytes countOffset maxRecords : UInt64)
    (header : Array CpiWord) (bump : UInt64) : UInt64 :=
  let _ := logAccount
  let _ := selfEntryTag
  let _ := authoritySeed
  let _ := maxBytes
  let _ := headerBytes
  let _ := countOffset
  let _ := maxRecords
  let _ := header
  let _ := bump
  0

/-- Append one compile-time-shaped record when `enabled != 0`. The component flushes before an
append that would exceed either the configured byte bound or record-count bound. -/
@[irreducible] def batchRecorderAppend
    (logAccount selfEntryTag : UInt64) (authoritySeed : String)
    (maxBytes headerBytes countOffset maxRecords : UInt64)
    (enabled : UInt64) (record : Array CpiWord) : UInt64 :=
  let _ := logAccount
  let _ := selfEntryTag
  let _ := authoritySeed
  let _ := maxBytes
  let _ := headerBytes
  let _ := countOffset
  let _ := maxRecords
  let _ := enabled
  let _ := record
  0

/-- Flush and close a bounded recorder. A header-only batch is emitted when no record was appended. -/
@[irreducible] def batchRecorderFinish
    (logAccount selfEntryTag : UInt64) (authoritySeed : String)
    (maxBytes headerBytes countOffset maxRecords : UInt64) : UInt64 :=
  let _ := logAccount
  let _ := selfEntryTag
  let _ := authoritySeed
  let _ := maxBytes
  let _ := headerBytes
  let _ := countOffset
  let _ := maxRecords
  0

/-! Official Solana program-memory host contracts. Static SDK spans lower to these leaves; the
host stubs cannot model account bytes and therefore return zero. Generated sBPF validates the
complete ranges and destination authorization before issuing the matching syscall. -/

@[irreducible] def memoryCopy
    (destinationAccount destinationOffset sourceAccount sourceOffset length : UInt64) : UInt64 :=
  let _ := destinationAccount
  let _ := destinationOffset
  let _ := sourceAccount
  let _ := sourceOffset
  let _ := length
  0

@[irreducible] def memoryMove
    (destinationAccount destinationOffset sourceAccount sourceOffset length : UInt64) : UInt64 :=
  let _ := destinationAccount
  let _ := destinationOffset
  let _ := sourceAccount
  let _ := sourceOffset
  let _ := length
  0

@[irreducible] def memoryCompare
    (leftAccount leftOffset rightAccount rightOffset length : UInt64) : UInt64 :=
  let _ := leftAccount
  let _ := leftOffset
  let _ := rightAccount
  let _ := rightOffset
  let _ := length
  0

@[irreducible] def memorySet
    (destinationAccount destinationOffset length byte : UInt64) : UInt64 :=
  let _ := destinationAccount
  let _ := destinationOffset
  let _ := length
  let _ := byte
  0

/-! Invocation-local bounded `Vec<u64>` leaves. Extraction requires compile-time capacity and
binds these stubs to one target-owned component. The host model cannot observe VM heap memory. -/

@[irreducible] def transientVecBegin (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientVecPush (capacity value : UInt64) : UInt64 :=
  let _ := capacity
  let _ := value
  0

@[irreducible] def transientVecSet (capacity index value : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  let _ := value
  0

@[irreducible] def transientVecTruncate (capacity newLength : UInt64) : UInt64 :=
  let _ := capacity
  let _ := newLength
  0

@[irreducible] def transientVecClear (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientVecFinish (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientVecLength (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientVecGet (capacity index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

@[irreducible] def transientVecPop (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

/-! Invocation-local bounded byte buffer leaves. Extraction requires compile-time byte capacity
and binds these stubs to one target-owned component; pushes and stores carry canonical `≤ 255`
byte values and `appendLe64` uses one 8-byte little-endian record. The host model cannot observe
VM heap memory. -/

@[irreducible] def transientBytesBegin (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBytesPush (capacity byte : UInt64) : UInt64 :=
  let _ := capacity
  let _ := byte
  0

@[irreducible] def transientBytesSet (capacity index byte : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  let _ := byte
  0

@[irreducible] def transientBytesTruncate (capacity newLength : UInt64) : UInt64 :=
  let _ := capacity
  let _ := newLength
  0

@[irreducible] def transientBytesClear (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBytesFinish (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBytesLength (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBytesGet (capacity index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

@[irreducible] def transientBytesPop (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBytesAppendLe64 (capacity value : UInt64) : UInt64 :=
  let _ := capacity
  let _ := value
  0

/-- Publish the current active byte-buffer payload as one official `sol_log_data` field. The host
model cannot observe VM heap memory; the target emitter binds the active pointer and length to the
syscall, and stale or mismatched handles keep the buffer's state error. -/
@[irreducible] def transientBytesLogData (capacity : UInt64) : UInt64 :=
  let _ := capacity
  0

/-- Open the invocation-local accumulators used by bounded FIFO cancellation. Persistent order and
trader state remains in account bytes; this handle contains only scalar cursor keys, event index,
and released-lot totals. -/
@[irreducible] def fifoCancelBegin : UInt64 :=
  0

/-- Cancel one statically described FIFO side in logical key order. All geometry and recorder
arguments must extract to constants. The supplied trader index is one-based; zero is a successful
no-op for the official missing-trader behavior. -/
@[irreducible] def fifoCancelSide
    (marketAccount rootWord linksWord parentWord priceWord sequenceWord ownerWord sizeWord
      lockedWord freeWord orderStride orderCapacity traderStride traderCapacity bid
      baseLotsPerBaseUnitWord tickSizeWord logAccount selfEntryTag : UInt64)
    (authoritySeed : String)
    (maxBytes headerBytes countOffset maxRecords traderIndex : UInt64) : UInt64 :=
  let _ := marketAccount
  let _ := rootWord
  let _ := linksWord
  let _ := parentWord
  let _ := priceWord
  let _ := sequenceWord
  let _ := ownerWord
  let _ := sizeWord
  let _ := lockedWord
  let _ := freeWord
  let _ := orderStride
  let _ := orderCapacity
  let _ := traderStride
  let _ := traderCapacity
  let _ := bid
  let _ := baseLotsPerBaseUnitWord
  let _ := tickSizeWord
  let _ := logAccount
  let _ := selfEntryTag
  let _ := authoritySeed
  let _ := maxBytes
  let _ := headerBytes
  let _ := countOffset
  let _ := maxRecords
  let _ := traderIndex
  0

/-- Cancel at most `cancelLimit` owned orders among the first `searchLimit` orders on one statically
described FIFO side, subject to the side's inclusive tick limit. `claimImmediately` is static:
withdrawal variants claim each released balance before returning, while free-funds variants retain
it in the trader slot. The traversal remains account-resident and bounded by fixed capacity. -/
@[irreducible] def fifoCancelUpToSide
    (marketAccount rootWord linksWord parentWord priceWord sequenceWord ownerWord sizeWord
      lockedWord freeWord orderStride orderCapacity traderStride traderCapacity bid
      baseLotsPerBaseUnitWord tickSizeWord logAccount selfEntryTag : UInt64)
    (authoritySeed : String)
    (maxBytes headerBytes countOffset maxRecords traderIndex tickLimit searchLimit cancelLimit
      claimImmediately : UInt64) : UInt64 :=
  let _ := marketAccount
  let _ := rootWord
  let _ := linksWord
  let _ := parentWord
  let _ := priceWord
  let _ := sequenceWord
  let _ := ownerWord
  let _ := sizeWord
  let _ := lockedWord
  let _ := freeWord
  let _ := orderStride
  let _ := orderCapacity
  let _ := traderStride
  let _ := traderCapacity
  let _ := bid
  let _ := baseLotsPerBaseUnitWord
  let _ := tickSizeWord
  let _ := logAccount
  let _ := selfEntryTag
  let _ := authoritySeed
  let _ := maxBytes
  let _ := headerBytes
  let _ := countOffset
  let _ := maxRecords
  let _ := traderIndex
  let _ := tickLimit
  let _ := searchLimit
  let _ := cancelLimit
  let _ := claimImmediately
  0

/-- Read aggregate quote lots released by the active FIFO cancellation handle. -/
@[irreducible] def fifoCancelQuoteReleased : UInt64 :=
  0

/-- Read aggregate base lots released by the active FIFO cancellation handle. -/
@[irreducible] def fifoCancelBaseReleased : UInt64 :=
  0

/-- Read the global event index after both sides; automatic recorder flushes never reset it. -/
@[irreducible] def fifoCancelEventCount : UInt64 :=
  0

/-- Close the invocation-local FIFO cancellation handle after its aggregate results were consumed. -/
@[irreducible] def fifoCancelFinish : UInt64 :=
  0

/-- `system.transfer`：普通包装，不是抽出特例。 -/
def systemTransfer (lamports : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    #[.u32le 2, .u64le lamports]

/-- CPI 到外层账户 1；空 metas、空 data。普通包装。 -/
def invokeAcc1 : UInt64 :=
  invoke 1 #[] #[]

/--
`system.createAccount`：payer / 新账户 / System。
owner 钉死为当前 program id。space 编译期常量。
-/
def systemCreate (lamports space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    -- bincode：u32 tag 0，无 pad；52 字节。
    #[.u32le 0, .u64le lamports, .u64le space, .programId]

/--
`system.assign`：把账户 0 的 owner 改成当前 program id。
外层：账户 0 s+w、System。
-/
def systemAssign : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 1, .programId]

/--
`system.allocate`：给账户 0 开 `space` 字节。space 编译期常量。
外层：账户 0 s+w、System。
-/
def systemAllocate (space : UInt64) : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 8, .u64le space]

/--
`system.allocateWithSeed`：给 `create_with_seed(acc0, "vault", program)` 开 `space` 字节。
种子本切片钉死。owner = 当前 program id。
外层：base s+w、派生账户 w、System。
-/
def systemAllocateWithSeed (space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- bincode：u32 tag 9 || base32 || u64le len || seed || space || owner32。
    #[.u32le 9, .accKey 0, .u64le 5, .ascii "vault", .u64le space, .programId]

/--
`system.createAccountWithSeed`：给 `create_with_seed(acc0, "vault", program)` 转 `lamports` 并开 `space` 字节。
种子本切片钉死。owner = 当前 program id。付款人兼 base。
外层：funder=base s+w、派生账户 w、System。
-/
def systemCreateWithSeed (lamports space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    -- bincode：u32 tag 3 || base32 || u64le len || seed || lamports || space || owner32。
    #[.u32le 3, .accKey 0, .u64le 5, .ascii "vault", .u64le lamports, .u64le space, .programId]

/--
`system.assignWithSeed`：把 `create_with_seed(acc0, "vault", program)` 的 owner 改成当前 program。
种子本切片钉死。
外层：base s+w、派生账户 w、System。
-/
def systemAssignWithSeed : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- bincode：u32 tag 10 || base32 || u64le len || seed || owner32。
    #[.u32le 10, .accKey 0, .u64le 5, .ascii "vault", .programId]

/--
`system.transferWithSeed`：从 `create_with_seed(acc0, "vault", program)` 转 `lamports` 到账户 2。
种子本切片钉死。from_owner = 当前 program id。
外层：base s+w、派生付款 w、收款 w、System。
-/
def systemTransferWithSeed (lamports : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false },
      { acc := 2, signer := false, writable := true }]
    -- bincode：u32 tag 11 || lamports || u64le len || seed || from_owner32。
    #[.u32le 11, .u64le lamports, .u64le 5, .ascii "vault", .programId]

/--
Token `InitializeMint2`：decimals 钉死 6，mint authority = acc0，freeze = None。
外层：authority s+w、mint w、Token。
-/
def tokenInitMint : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    -- packed：u8 tag 20 || u8 decimals || mint_authority32 || COption None。
    #[.u8le 20, .u8le 6, .accKey 0, .u8le 0]

/--
Token `SyncNative`：把 native token 账户的 amount 同步成底层 lamports。
外层账户 0 只为统一 CPI 区保留；native 账户 w、Token。SyncNative 不要求 owner 签名。
-/
def tokenSyncNative : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    #[.u8le 17]

/--
Token `TransferChecked`：普通包装。decimals 编译期常量。
外层 0 必须是 authority（prelude 强制 acc0 signer）。
内层账户按官方顺序：source / mint / dest / authority。
-/
def tokenTransferChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- packed：u8 tag 12 || u64le amount || u8 decimals。
    #[.u8le 12, .u64le amount, .u8le decimals]

/--
Token-2022 `TransferChecked` for the classic-compatible base slice, guarded by the bounded
TLV account-data policy. The transaction must place the Token-2022 program at external index 4.
The official state-with-extensions layout is parsed by a target-local bounded cursor before any
CPI: the classic base mint/account (82/165 bytes) proceeds; an extension-form account proceeds
only when its TLV region holds nothing but official end/padding forms; every real extension
entry — transfer-fee, transfer-hook, or anything else — is rejected atomically with a classified
reason, before any persistent write or CPI, until its complete official semantics, accounts, and
CPI behavior are modeled.
-/
def token2022TransferChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true,
        accountData := some (.token2022Base .account) },
      { acc := 2, signer := false, writable := false,
        accountData := some (.token2022Base .mint) },
      { acc := 3, signer := false, writable := true,
        accountData := some (.token2022Base .account) },
      { acc := 0, signer := true, writable := false }]
    -- Token and Token-2022 share the packed tag-12 layout.
    #[.u8le 12, .u64le amount, .u8le decimals]

/--
Token `TransferChecked` with a statically indexed outer account recipe. Every index must reduce
to a literal during extraction. This is the multi-vault form of `tokenTransferChecked`; the
authority is an ordinary transaction signer.
-/
def tokenTransferCheckedIx (programIx sourceIx mintIx destinationIx authorityIx amount decimals :
    UInt64) : UInt64 :=
  invoke programIx
    #[{ acc := sourceIx, signer := false, writable := true },
      { acc := mintIx, signer := false, writable := false },
      { acc := destinationIx, signer := false, writable := true },
      { acc := authorityIx, signer := true, writable := false }]
    #[.u8le 12, .u64le amount, .u8le decimals]

/--
Statically indexed Token `TransferChecked` whose authority is a PDA signer group. `seeds` does
not include the final bump. The Solana runtime grants signer privilege only when the derived key
matches `authorityIx`.
-/
def tokenTransferCheckedSignedIx
    (programIx sourceIx mintIx destinationIx authorityIx amount decimals : UInt64)
    (seeds : Array PdaSeed) (bump : UInt64) : UInt64 :=
  invokeSignedSeeds programIx
    #[{ acc := sourceIx, signer := false, writable := true },
      { acc := mintIx, signer := false, writable := false },
      { acc := destinationIx, signer := false, writable := true },
      { acc := authorityIx, signer := true, writable := false }]
    #[.u8le 12, .u64le amount, .u8le decimals]
    seeds bump

/--
Statically indexed classic SPL Token `Transfer` whose authority is a PDA signer group. This is the
unchecked tag-3 wire used by protocols whose authenticated account header already fixes the mint;
unlike `TransferChecked`, its account metas are source / destination / authority and no mint account
or decimals byte is present. `seeds` remains compile-time-shaped and does not include the bump.
-/
def tokenTransferSignedIx
    (programIx sourceIx destinationIx authorityIx amount : UInt64)
    (seeds : Array PdaSeed) (bump : UInt64) : UInt64 :=
  invokeSignedSeeds programIx
    #[{ acc := sourceIx, signer := false, writable := true },
      { acc := destinationIx, signer := false, writable := true },
      { acc := authorityIx, signer := true, writable := false }]
    #[.u8le 3, .u64le amount]
    seeds bump

/--
Token `MintToChecked`：普通包装。decimals 编译期常量。
外层 0 是 mint authority。内层：mint w / dest w / authority。
-/
def tokenMintToChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 14, .u64le amount, .u8le decimals]

/--
Token `BurnChecked`：普通包装。decimals 编译期常量。
外层 0 是 token owner。内层：source w / mint w / authority。
-/
def tokenBurnChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 15, .u64le amount, .u8le decimals]

/--
Token `InitializeAccount3`：普通包装。owner = 外层账户 0 公钥。
外层 0 是 owner。内层：account w / mint r。
-/
def tokenInitAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false }]
    #[.u8le 18, .accKey 0]

/--
Token `CloseAccount`：普通包装。
外层 0 是 owner。内层：source w / dest w / owner s。
-/
def tokenCloseAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 9]

/--
Token `ApproveChecked`：普通包装。decimals 编译期常量。
外层 0 是 owner。内层：source w / mint r / delegate r / owner s。
-/
def tokenApproveChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 13, .u64le amount, .u8le decimals]

/--
Token `FreezeAccount`：普通包装。
外层 0 是 mint freeze authority。内层：account w / mint r / authority s。
-/
def tokenFreezeAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 10]

/--
Token `ThawAccount`：普通包装。账户表与 Freeze 相同。
-/
def tokenThawAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 11]

/--
Token `SetAuthority`：普通包装。本切片钉死 `MintTokens`，
新 authority = 外层账户 2 公钥。
外层 0 是当前 mint authority。内层：mint w / current authority s。
-/
def tokenSetMintAuthority : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 0, .u8le 1, .accKey 2]

/--
Token `SetAuthority`：`AccountOwner`。新 owner = 外层账户 2。
外层 0 是当前 owner。内层：account w / current owner s。
-/
def tokenSetAccountAuthority : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 2, .u8le 1, .accKey 2]

/--
Token 未检查 `Approve`（tag 4）。decimals 不进 data。
外层 0 是 owner。内层：source w / delegate r / owner s。
-/
def tokenApprove (amount : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 4, .u64le amount]

/--
Token `InitializeMultisig2`（tag 19，不吃 Rent sysvar）。
本切片钉死 m=2，两个 signer = acc2 / acc3。
内层：multisig w / signer0 r / signer1 r。callee 是外层账户 4。
-/
def tokenInitMultisig : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false }]
    #[.u8le 19, .u8le 2]

/--
System `AdvanceNonceAccount`（tag 4）。
外层 0 是 nonce authority。内层：nonce w / recent blockhashes r / authority s。
callee 是外层账户 3（System）。
-/
def systemAdvanceNonce : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 4]

/--
Token `Revoke`：普通包装。清掉 source 的 delegate。
外层 0 是 owner。内层：source w / owner s。
-/
def tokenRevoke : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 5]

/--
最近一次 CPI 的 8 字节返回。抽出后发射 `sol_get_return_data`。
宿主侧是不可约 stub。无 CPI / 长度不是 8 链上 Custom(1)。
完整 program id / 变长缓冲本剖面 fail closed。
-/
@[irreducible] def cpiReturn : UInt64 := 0

/--
Token `GetAccountDataSize`：普通包装。
外层 1 是 mint，callee 是外层账户 2。返回值走 `cpiReturn`。
-/
def tokenAccountSize : UInt64 :=
  let _ := invoke 2
    #[{ acc := 1, signer := false, writable := false }]
    #[.u8le 21]
  cpiReturn

/--
Memo 写一条 UTF-8 字面量。本切片钉死 `"ok"`。
外层 0 是 signer；callee 是外层账户 1。
-/
def memoWrite : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.ascii "ok"]

/--
找当前 program id 下、一条 ASCII 种子的 canonical bump。
抽出器认这个名字，发射 `sol_try_find_program_address`。
宿主侧是不可约 stub，返回 0，不要当链上 bump 用。
完整 32B key / 多种子 / 指定 program id 本剖面 fail closed。
-/
@[irreducible] def findPda (seed : String) : UInt64 :=
  let _ := seed
  0

/--
Find the canonical bump for a compile-time-shaped seed list under the current program id.
Account-key seeds refer to the authenticated account table; arbitrary runtime byte buffers and
alternate program ids remain fail closed.
-/
@[irreducible] def findPdaSeeds (seeds : Array PdaSeed) : UInt64 :=
  let _ := seeds
  0

/--
Check that one statically indexed external account is the canonical PDA for a compile-time-shaped
seed list under the current program id. Like CPI metas and `PdaSeed.accKey`, `accountIx` is relative
to the external-account region: physical account 0 is the generated state account or a raw
adapter's declared program account. Returns 0 on equality and 1 otherwise. The full 32-byte key
comparison is emitted by the SVM backend; the host definition is an irreducible stub.
-/
@[irreducible] def checkPdaSeeds (accountIx : UInt64) (seeds : Array PdaSeed) : UInt64 :=
  let _ := accountIx
  let _ := seeds
  0

/--
当前 program id + 一条 ASCII 种子 + bump 是否是合法 PDA。
抽出后发射 `sol_create_program_address`。成功 0，失败 1。
宿主侧是不可约 stub，返回 0。它不接收目标账户；需要完整 32B key 相等时使用
`checkPdaSeeds`。
-/
@[irreducible] def checkPda (seed : String) (bump : UInt64) : UInt64 :=
  let _ := seed
  let _ := bump
  0

/--
给当前 program 下、种子 `"vault"` 的 PDA 开 16 字节。
PDA 用 `findPda` 的 bump 签字。space 本切片钉死。
-/
def createPda (lamports : UInt64) : UInt64 :=
  invokeSigned 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    #[.u32le 0, .u64le lamports, .u64le 16, .programId]
    "vault" (findPda "vault")

/--
Bounded remaining-account view: read header metadata of the runtime-selected remaining account
`base + index`. The compile-time window `[base, base + capacity)` must bound the index; the target
additionally validates `base + index` against the available account count, then reuses the account
header walk in place. Any violation exits `Custom(1)` atomically. Host side is an irreducible stub.
Persistent state is never addressed through a view; views are read-only.
-/
@[irreducible] def viewLamports (base capacity index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := index
  0

/-- `data_len` of the runtime-selected remaining account `base + index`. Bounds as `viewLamports`. -/
@[irreducible] def viewDataLen (base capacity index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := index
  0

/-- `is_signer` (0 or 1) of the runtime-selected remaining account `base + index`. Bounds as
`viewLamports`. This reads the flag; forcing entry-level signer policy stays with the entry. -/
@[irreducible] def viewIsSigner (base capacity index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := index
  0

/-- `is_writable` (0 or 1) of the runtime-selected remaining account `base + index`. Bounds as
`viewLamports`. -/
@[irreducible] def viewIsWritable (base capacity index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := index
  0

/--
First `word`-th little-endian u64 (word 0..=3) of the runtime-selected remaining account's public
key. `base`, `capacity`, and `word` must be extraction-time constants; only `index` is dynamic.
-/
@[irreducible] def viewKeyWord (base capacity word index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := word
  let _ := index
  0

/--
Whether the runtime-selected remaining account `base + index` is owned by the current program id.
Equal returns 0, otherwise 1. Full 32-byte comparison is emitted by the SVM target.
-/
@[irreducible] def viewOwnerIsSelf (base capacity index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := index
  0

/--
Read one little-endian u64 at word `word` of the runtime-selected remaining account's data. The
target validates the index against both the compile-time capacity and the available account count,
then checks `data_len ≥ 8 * (word + 1)` before forming the data pointer. Any failure is an atomic
`Custom(1)` exit. This is a zero-copy read of the serialized account input; it does not allocate
or copy account data.
-/
@[irreducible] def viewDataWord (base capacity word index : UInt64) : UInt64 :=
  let _ := base
  let _ := capacity
  let _ := word
  let _ := index
  0

/-- 账户 0 的 lamports。只读；改余额走 `systemTransfer`。 -/
@[irreducible] def accLamports0 : UInt64 := 0

/-- 账户 0 owner 的第一个小端 `u64`。不是完整 32B。 -/
@[irreducible] def accOwner0 : UInt64 := 0

/-- 账户 0 `data_len`。只读。 -/
@[irreducible] def accDataLen0 : UInt64 := 0

/-- `NUM_ACCOUNTS`。只读；不开放 remaining accounts。 -/
@[irreducible] def accN : UInt64 := 0

/-- 账户 0 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner0 : UInt64 := 0

/-- 账户 0 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable0 : UInt64 := 0

/-- 账户 0 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable0 : UInt64 := 0

/-- 账户 1 的 lamports。只读。 -/
@[irreducible] def accLamports1 : UInt64 := 0

/-- 账户 1 owner 的第一个小端 `u64`。不是完整 32B。 -/
@[irreducible] def accOwner1 : UInt64 := 0

/-- 账户 1 `data_len`。只读。 -/
@[irreducible] def accDataLen1 : UInt64 := 0

/-- 账户 1 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner1 : UInt64 := 0

/-- 账户 1 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable1 : UInt64 := 0

/-- 账户 1 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable1 : UInt64 := 0

/--
编译期 ASCII 字面量的 SHA-256。抽出器认这个名字，发射 `sol_sha256`。
返回 32 字节 digest 的第一个小端 `u64`。宿主侧是不可约 stub，返回 0。
完整 32B / 多切片 / 运行时缓冲 / blake3 / poseidon 本剖面 fail closed。
-/
@[irreducible] def sha256Lit (seed : String) : UInt64 :=
  let _ := seed
  0

/--
编译期 ASCII 字面量的 Keccak-256（Ethereum，不是 FIPS SHA3-256）。
抽出器认这个名字，发射 `sol_keccak256`。
返回 32 字节 digest 的第一个小端 `u64`。宿主侧是不可约 stub，返回 0。
完整 32B / 多切片 / 运行时缓冲 / blake3 / poseidon 本剖面 fail closed。
-/
@[irreducible] def keccak256Lit (seed : String) : UInt64 :=
  let _ := seed
  0

/--
账户 `acc` 公钥的第 `word` 个小端 `u64`（`word` 0..=3）。
`acc` / `word` 必须在抽出时是常量。`acc ≥ 1` 走 walk，不强制入口签名。
这不是 `signerKey0`：读 key 字不检查 `is_signer`。
`acc ≥ Svm.ABI.maxTxAccountLocks` 或运行时下标本剖面 fail closed。
-/
@[irreducible] def accKeyWord (acc word : UInt64) : UInt64 :=
  let _ := acc
  let _ := word
  0

/--
账户 `acc` owner 的第 `word` 个小端 `u64`（`word` 0..=3）。
`acc` / `word` 必须在抽出时是常量。`acc ≥ 1` 走 walk。
`acc ≥ Svm.ABI.maxTxAccountLocks` 或运行时下标本剖面 fail closed。
-/
@[irreducible] def accOwnerWord (acc word : UInt64) : UInt64 :=
  let _ := acc
  let _ := word
  0

/--
账户 `acc` data 的第 `word` 个小端 `u64`。`acc` / `word` 必须在抽出时是常量；
`acc ≥ 1` 走 walk。目标发射器先检查 `data_len ≥ 8 * (word + 1)`，越界以
`Custom(1)` fail closed，不返回零值冒充账户内容。
-/
@[irreducible] def accDataWord (acc word : UInt64) : UInt64 :=
  let _ := acc
  let _ := word
  0

/--
账户 `acc` 的固定 stride 槽中第 `index` 个 u64。`acc`、`baseWord`、`strideWords` 和
`capacity` 必须在抽出时是常量，只有零基 `index` 可在运行时选择。目标发射器先检查
`index < capacity`，再检查计算出的 word 位于账户 `data_len` 内；任一失败都以
`Custom(1)` fail closed。这是账户内 zero-copy 读取，不分配或复制槽数组。
-/
@[irreducible] def accDataWordAt
    (acc baseWord strideWords capacity index : UInt64) : UInt64 :=
  let _ := acc
  let _ := baseWord
  let _ := strideWords
  let _ := capacity
  let _ := index
  0

/--
Read one u64 field by the one-based index returned from an account-resident map lookup. Static
geometry has the same constraints as `accDataWordAt`, but index zero is the null sentinel and is
rejected before normalization. This lets source code compose `map find → field read` without
forming a pointer or manually translating persistent indexes.
-/
@[irreducible] def accDataWordAtOneBased
    (acc baseWord strideWords capacity index : UInt64) : UInt64 :=
  let _ := acc
  let _ := baseWord
  let _ := strideWords
  let _ := capacity
  let _ := index
  0

/--
Search a statically shaped account-resident red-black tree by a four-word key and return its
one-based slot index, or zero when absent. Account/root/field geometry and capacity must be
compile-time constants; only the key is dynamic. The target performs at most 64 checked links and
byte-compares the original 32 key bytes. This lookup does not allocate, copy nodes, or expose a
pointer; callers that require complete topology/allocator assurance compose it after
`accDataRbTreeKey4Valid`.
-/
@[irreducible] def accDataRbTreeKey4Find
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity
      key0 key1 key2 key3 : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := key0
  let _ := key1
  let _ := key2
  let _ := key3
  0

/--
Search a statically shaped two-word FIFO tree by `(key0, key1)` and return its one-based slot index,
or zero when absent. `bid=1` selects descending ordering for both words and `bid=0` ascending
ordering. Geometry is compile-time fixed and traversal is bounded to 64 checked links; no heap map,
node copy, raw pointer, or persistent allocation is created. Callers compose the complete FIFO tree
validator when malformed topology must be rejected before business logic.
-/
@[irreducible] def accDataRbTreeOrderFind
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid
      price sequence : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := price
  let _ := sequence
  0

/--
Return the first two-word FIFO slot when `hasCursor=0`, or the strict logical successor of
`(key0, key1)` when `hasCursor=1`. The result is a one-based slot index or zero at the end. Every
call restarts from the fixed account-resident root, so callers retain only the scalar key across
removals; no node pointer, heap collection, or runtime geometry is created.
-/
@[irreducible] def accDataRbTreeOrderCursor
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid
      hasCursor price sequence : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := hasCursor
  let _ := price
  let _ := sequence
  0

/--
Write one u64 in a fixed-stride slot of an external account. `acc ≥ 1`, `baseWord`,
`strideWords`, and `capacity` must be compile-time constants; only the zero-based `index` and
`value` are dynamic. The SVM target requires the account to be writable and owned by the current
program, then checks both the capacity and final `data_len` before storing. Failure is `Custom(1)`
and occurs before this write. This is persistent account storage, not transient heap allocation.
-/
@[irreducible] def accDataWordSetAt
    (acc baseWord strideWords capacity index value : UInt64) : UInt64 :=
  let _ := acc
  let _ := baseWord
  let _ := strideWords
  let _ := capacity
  let _ := index
  let _ := value
  0

/--
Write one u64 field by a one-based account-resident map index. Index zero is rejected as the null
sentinel; account geometry remains compile-time fixed and the target still requires a writable,
current-program-owned external account. This is the mutation twin of
`accDataWordAtOneBased`, not a heap or pointer store.
-/
@[irreducible] def accDataWordSetAtOneBased
    (acc baseWord strideWords capacity index value : UInt64) : UInt64 :=
  let _ := acc
  let _ := baseWord
  let _ := strideWords
  let _ := capacity
  let _ := index
  let _ := value
  0

/--
Insert one dynamic four-word key into a statically shaped, account-resident red-black tree. The
tree header is four words (`root`, padding, `size`, packed bump/free cursor); node links,
parent/color, key, stride, and capacity are compile-time constants. The SVM target first requires
the external account to be writable and current-program-owned, then validates the complete tree
and allocator partition before checking duplicate/full conditions. It performs bounded in-place
search, Sokoban bump/free-list allocation, complete slot initialization, and general insertion
fixup. Persistent state contains only one-based addresses and the zero sentinel; no heap, Map,
node copy, raw pointer, or detached allocation is exposed.
-/
@[irreducible] def accDataRbTreeKey4Insert
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity
      key0 key1 key2 key3 : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := key0
  let _ := key1
  let _ := key2
  let _ := key3
  0

/--
Checked-add two values in a record keyed by four little-endian 64-bit limbs. The SVM target validates
the fixed account-resident key4 tree, then either updates an existing record or inserts a canonical
zeroed record with those two values. No heap map or persistent pointer is created.
-/
@[irreducible] def accDataRbTreeTraderDeposit
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity
      key0 key1 key2 key3 quoteLots baseLots : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := key0
  let _ := key1
  let _ := key2
  let _ := key3
  let _ := quoteLots
  let _ := baseLots
  0

/--
Remove one dynamic four-word key from a statically shaped, account-resident red-black tree. The
SVM target validates the complete tree and allocator partition before searching. It then performs
the Sokoban predecessor transplant, bounded delete fixup, and free-list push in place. Persistent
state remains one-based indexes plus the zero sentinel; the removed slot's key/value payload stays
account-resident until a later bounded insertion reinitializes that slot.
-/
@[irreducible] def accDataRbTreeKey4Remove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity
      key0 key1 key2 key3 : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := key0
  let _ := key1
  let _ := key2
  let _ := key3
  0

/--
Insert one four-word value into a statically shaped, account-resident two-word FIFO red-black tree.
The key is `(key0, key1)` and `bid` selects descending or ascending order for both words. The SVM
target validates the complete tree/free partition and incoming direction tag before the first
store, supports in-place duplicate-value replacement, and otherwise performs bounded
bump/free-list allocation plus insertion fixup. No persistent pointer or heap container is created.
-/
@[irreducible] def accDataRbTreeOrderInsert
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid
      price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp : UInt64) :
    UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := price
  let _ := sequence
  let _ := traderIndex
  let _ := numBaseLots
  let _ := lastValidSlot
  let _ := lastValidUnixTimestamp
  0

/--
Remove one key from a statically shaped, account-resident two-word FIFO red-black tree. The SVM
target validates the complete tree/free partition and encoded direction tag before the first store,
then performs bounded predecessor transplant, delete fixup, and free-list push. The removed
key/value payload remains in its fixed account slot until a later insertion reinitializes that slot;
no persistent pointer or heap container is created.
-/
@[irreducible] def accDataRbTreeOrderRemove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid
      price sequence : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := price
  let _ := sequence
  0

/--
Update one word in an existing account-resident ordered-map record, removing the keyed record when
the new value is zero. Static arguments describe the map and selected field; only key, one-based
slot, and value are dynamic. This is a reusable bounded-storage policy, not a protocol operation.
-/
@[irreducible] def accDataRbTreeOrderSetWordOrRemove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord valueBaseWord
      strideWords capacity bid price sequence index value : UInt64) : UInt64 :=
  let _ := acc
  let _ := rootWord
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := valueBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := price
  let _ := sequence
  let _ := index
  let _ := value
  0

/--
沿账户内 fixed-stride 节点的 parent 链验证一条有界路径。静态参数指定 links word、
parent/color word、stride、capacity 和最多 64 步；运行时只提供起点、root 和 allocator
`bumpIndex`。目标发射器逐步验证 index envelope、颜色、parent→child reciprocity，并要求
在 `maxDepth` 内到达 parent/color=0 的 root。它只保留当前 index/depth，不分配 visited
Map，不复制节点；短账户在形成 data pointer 前 `Custom(1)`。
-/
@[irreducible] def accDataParentPathValid
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth
      index root bumpIndex : UInt64) : UInt64 :=
  let _ := acc
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := maxDepth
  let _ := index
  let _ := root
  let _ := bumpIndex
  0

/--
直接在账户数据中验证完整的 fixed-capacity Sokoban red-black tree 及 allocator partition。
静态参数选择 links、parent/color、两个 key word 和槽布局；`bid=1` 使用双字降序，
`bid=0` 使用双字升序。目标发射器使用固定的 4096-bit 栈 bitmap，不分配 Map、
不复制节点；它验证树结构、颜色/black height、FIFO key 顺序、live count，以及 free-list
与所有 pre-bump 槽的精确分区。
-/
@[irreducible] def accDataRbTreeValid
    (acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid
      root size bumpIndex freeListHead : UInt64) : UInt64 :=
  let _ := acc
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := sequenceBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := bid
  let _ := root
  let _ := size
  let _ := bumpIndex
  let _ := freeListHead
  0

/--
直接在账户数据中验证以四个连续 u64 存放 32-byte key 的 fixed-capacity red-black tree。
key 按原始 unsigned bytes 做 strict lexicographic ascending 比较；目标发射器用固定
8321-bit bitmap 和 64-entry traversal stack，不分配 heap/Map，不复制节点。除 red-black
结构和 key ordering 外，它还验证 reachable live count 以及 allocator 的 exact live/free
partition。
-/
@[irreducible] def accDataRbTreeKey4Valid
    (acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity
      root size bumpIndex freeListHead : UInt64) : UInt64 :=
  let _ := acc
  let _ := linksBaseWord
  let _ := parentBaseWord
  let _ := keyBaseWord
  let _ := strideWords
  let _ := capacity
  let _ := root
  let _ := size
  let _ := bumpIndex
  let _ := freeListHead
  0

/--
账户 `acc` 的 lamports。`acc` 必须在抽出时是常量，且
`acc < Svm.ABI.maxTxAccountLocks`（官方当前强制 64）。
`acc ≥ 1` 走 walk。旧名 `accLamports0` / `accLamports1` 仍独立。
-/
@[irreducible] def accLamports (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `data_len`。`acc < Svm.ABI.maxTxAccountLocks`，抽出时常量。 -/
@[irreducible] def accDataLen (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/--
账户 `acc` 公钥的第一个小端 `u64`。用到这个叶子的入口会检查该账户 `is_signer`。
`acc < Svm.ABI.maxTxAccountLocks`。这不是 `tx.origin`。旧名 `signerKey0` 仍独立。
-/
@[irreducible] def signerKey (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/--
账户 `acc` 的 owner 是否是当前 program id。
抽出后比 32B。相等返回 0，不等返回 1。`acc < Svm.ABI.maxTxAccountLocks`。
-/
@[irreducible] def ownerIsSelf (acc : UInt64) : UInt64 :=
  let _ := acc
  0

end ProofForge.Svm.Runtime
