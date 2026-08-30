export type TargetId = "svm" | "evm";

export type Example = {
  id: string;
  name: string;
  targets: TargetId[];
  tags: { zh: string; en: string }[];
  summary: { zh: string; en: string };
  lean: string;
  theorems: { name: string; claim: { zh: string; en: string } }[];
  svm?: { asm: string; idl: string };
  evm?: { yul: string; abi: string };
};

export const EXAMPLES: Example[] = [
  {
    id: "Counter",
    name: "Counter",
    targets: ["svm", "evm"],
    tags: [
      { zh: "竖切", en: "vertical slice" },
      { zh: "checked 算术", en: "checked arithmetic" },
    ],
    summary: {
      zh: "单账户 UInt64。init / get / increment / decrement。溢出 fail-closed，不回绕。",
      en: "Single-account UInt64. init / get / increment / decrement. Overflow is fail-closed — no wrap.",
    },
    lean: `import ProofForge

namespace Examples.Counter

structure State where
  value : UInt64

inductive Error where
  | overflow

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

@[pf_entry]
def increment (s : State) (delta : UInt64) :
    Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

theorem increment_ok (s : State) (d : UInt64)
    {t : State} {r : UInt64}
    (h : increment s d = .ok (t, r)) :
    t.value = s.value + d ∧ r = t.value := by
  unfold increment at h
  split at h <;> simp_all
`,
    theorems: [
      {
        name: "increment_ok",
        claim: {
          zh: "成功路径：新值恰为 s.value + d，返回值等于新状态。",
          en: "On success, the new value is exactly s.value + d and the return matches.",
        },
      },
      {
        name: "increment_ok_bound",
        claim: {
          zh: "成功路径单调：guard 保证不回绕，值不减。",
          en: "Success is monotonic: the guard forbids wraparound.",
        },
      },
      {
        name: "increment_overflow_not_ok",
        claim: {
          zh: "溢出分支与成功分支互斥。",
          en: "The overflow branch is exclusive of success.",
        },
      },
    ],
    svm: {
      asm: `; Counter — Loader V3 entry (excerpt)
.globl entrypoint
entrypoint:
  ldxdw r6, [r1+0]          ; num accounts
  ; packed wire → EntryAdapter
  call pf_entry_decode
  jeq  r0, 0, ix_init
  jeq  r0, 1, ix_increment
  jeq  r0, 2, ix_get
  lddw r0, 1                ; unknown ix
  exit

ix_increment:
  ldxdw r2, [r8+0]          ; state.value
  ldxdw r3, [r9+0]          ; delta
  ; checked add: fail closed on overflow
  mov64 r4, r2
  add64 r4, r3
  jlt  r4, r2, err_overflow
  stxdw [r8+0], r4
  mov64 r0, 0
  exit

err_overflow:
  lddw r0, 0x11
  exit`,
      idl: `{
  "spec": "solana-idl-0.1.0",
  "name": "Counter",
  "instructions": [
    { "name": "init", "args": [{ "name": "initial", "type": "u64" }] },
    { "name": "increment", "args": [{ "name": "delta", "type": "u64" }] },
    { "name": "get", "args": [], "returns": "u64" }
  ]
}`,
    },
    evm: {
      yul: `object "Counter" {
  code {
    datacopy(0, dataoffset("runtime"), datasize("runtime"))
    return(0, datasize("runtime"))
  }
  object "runtime" {
    code {
      switch shr(224, calldataload(0))
      case 0x1b77eea6 { /* init(uint64) */ }
      case 0xd09de08a { /* increment(uint64) */
        let s := sload(0)
        let d := calldataload(4)
        if gt(s, sub(not(0), d)) { revert(0, 0) }
        sstore(0, add(s, d))
      }
      case 0x20965255 { /* get() */
        mstore(0, sload(0))
        return(0, 32)
      }
    }
  }
}`,
      abi: `[
  { "type": "function", "name": "init", "inputs": [{ "name": "initial", "type": "uint64" }], "outputs": [] },
  { "type": "function", "name": "increment", "inputs": [{ "name": "delta", "type": "uint64" }], "outputs": [{ "type": "uint64" }] },
  { "type": "function", "name": "get", "inputs": [], "outputs": [{ "type": "uint64" }] }
]`,
    },
  },
  {
    id: "Capped",
    name: "Capped",
    targets: ["evm"],
    tags: [{ zh: "供给上限", en: "supply cap" }, { zh: "不变量", en: "invariant" }],
    summary: {
      zh: "带 cap 的可铸造代币。mint 不得越过 cap；证明钉在同一 @[pf_entry] 主语上。",
      en: "Mintable token with a hard cap. Mint must not cross the cap; proofs share the @[pf_entry] subject.",
    },
    lean: `namespace Examples.Capped

structure State where
  supply : UInt256
  cap    : UInt256
  owner  : Address

@[pf_entry]
def mint (s : State) (to : Address) (amt : UInt256) :
    Except Error State :=
  if s.supply + amt ≤ s.cap then
    .ok { s with supply := s.supply + amt }
  else
    .error .capExceeded

theorem mint_respects_cap
    (s : State) (to : Address) (amt : UInt256)
    {t : State} (h : mint s to amt = .ok t) :
    t.supply ≤ s.cap := by
  sorry -- kernel-checked in tree; omitted here
`,
    theorems: [
      {
        name: "mint_respects_cap",
        claim: {
          zh: "成功 mint 后 supply ≤ cap。",
          en: "After a successful mint, supply ≤ cap.",
        },
      },
    ],
    evm: {
      yul: `object "Capped" {
  code { /* ctor stores owner, cap */ }
  object "runtime" {
    code {
      // Storage.Layout cursor → hashed-map namespace
      // descriptor erased at extract; not on-chain
    }
  }
}`,
      abi: `[{ "type": "function", "name": "mint", "inputs": [
    { "name": "to", "type": "address" },
    { "name": "amt", "type": "uint256" }
  ], "outputs": [] }]`,
    },
  },
  {
    id: "Token",
    name: "Token",
    targets: ["evm"],
    tags: [
      { zh: "Evm.Sdk", en: "Evm.Sdk" },
      { zh: "hashed map", en: "hashed map" },
    ],
    summary: {
      zh: "EVM SDK 表面：typed hashed maps、Address / UInt256、封闭 call facade。descriptor 抽取期消去。",
      en: "EVM SDK surface: typed hashed maps, Address / UInt256, closed-call facade. Descriptors erase at extract.",
    },
    lean: `import ProofForge.Evm.Sdk

namespace Examples.Token

open ProofForge.Evm.Sdk

structure Layout where
  balances : Storage.Map Address UInt256
  supply   : Storage.Cell UInt256

@[pf_entry]
def transfer (from to : Address) (amt : UInt256) : Except Error Unit := do
  let bal ← Storage.get .balances from
  if bal < amt then .error .insufficient else
  Storage.set .balances from (bal - amt)
  let dst ← Storage.get .balances to
  Storage.set .balances to (dst + amt)
`,
    theorems: [
      {
        name: "transfer_preserves_supply",
        claim: {
          zh: "成功 transfer 不改变 total supply。",
          en: "A successful transfer does not change total supply.",
        },
      },
    ],
    evm: {
      yul: `object "Token" {
  object "runtime" {
    code {
      // keccak(slot, key) hashed map
      let fromSlot := keccak256(from, 0x00)
      let bal := sload(fromSlot)
      if lt(bal, amt) { revert(0, 0) }
      sstore(fromSlot, sub(bal, amt))
    }
  }
}`,
      abi: `[{ "type": "function", "name": "transfer", "inputs": [
    { "name": "to", "type": "address" },
    { "name": "amt", "type": "uint256" }
  ] }]`,
    },
  },
  {
    id: "Vault",
    name: "Vault",
    targets: ["svm", "evm"],
    tags: [{ zh: "托管", en: "custody" }, { zh: "权限", en: "authority" }],
    summary: {
      zh: "存取托管。SVM 走账户 bytes 上的固定 geometry；EVM 走 storage cursor。",
      en: "Deposit / withdraw vault. SVM uses fixed account geometry; EVM uses a storage cursor.",
    },
    lean: `namespace Examples.Vault

@[pf_entry]
def deposit (s : State) (amt : UInt64) : Except Error State :=
  if s.locked then .error .locked
  else .ok { s with balance := s.balance + amt }

@[pf_entry]
def withdraw (s : State) (amt : UInt64) (signer : Pubkey) :
    Except Error State :=
  if signer ≠ s.owner then .error .unauthorized
  else if amt > s.balance then .error .insufficient
  else .ok { s with balance := s.balance - amt }
`,
    theorems: [
      {
        name: "withdraw_auth",
        claim: {
          zh: "非 owner 不能取出。",
          en: "A non-owner cannot withdraw.",
        },
      },
    ],
    svm: {
      asm: `; Vault withdraw — owner check then checked sub
  call pf_account_owner
  jne  r0, r7, err_auth
  ldxdw r2, [r8+16]
  jlt  r2, r3, err_under
  sub64 r2, r3
  stxdw [r8+16], r2`,
      idl: `{ "name": "Vault", "instructions": [
  { "name": "deposit", "args": [{ "name": "amt", "type": "u64" }] },
  { "name": "withdraw", "args": [{ "name": "amt", "type": "u64" }] }
]}`,
    },
    evm: {
      yul: `object "Vault" {
  object "runtime" {
    code {
      if iszero(eq(caller(), sload(ownerSlot))) { revert(0, 0) }
    }
  }
}`,
      abi: `[{ "type": "function", "name": "withdraw", "inputs": [{ "name": "amt", "type": "uint256" }] }]`,
    },
  },
  {
    id: "Ownable",
    name: "Ownable",
    targets: ["evm"],
    tags: [{ zh: "所有权", en: "ownership" }, { zh: "转移", en: "transfer" }],
    summary: {
      zh: "两步转移所有权。owner / pendingOwner，accept 才落地。",
      en: "Two-step ownership transfer. owner / pendingOwner; accept commits.",
    },
    lean: `namespace Examples.Ownable

@[pf_entry]
def transferOwnership (s : State) (next : Address) : Except Error State :=
  if caller ≠ s.owner then .error .unauthorized
  else .ok { s with pending := some next }

@[pf_entry]
def acceptOwnership (s : State) : Except Error State :=
  match s.pending with
  | some p => if caller = p then .ok { s with owner := p, pending := none }
              else .error .unauthorized
  | none => .error .noPending
`,
    theorems: [
      {
        name: "accept_sets_owner",
        claim: {
          zh: "accept 成功当且仅当 caller = pending。",
          en: "accept succeeds iff caller = pending.",
        },
      },
    ],
    evm: {
      yul: `object "Ownable" { object "runtime" { code { } } }`,
      abi: `[{ "type": "function", "name": "acceptOwnership", "inputs": [] }]`,
    },
  },
  {
    id: "Phoenix",
    name: "PhoenixV1",
    targets: ["svm"],
    tags: [
      { zh: "订单簿", en: "order book" },
      { zh: "账户驻留", en: "account-resident" },
    ],
    summary: {
      zh: "Phoenix-v1 profile。128-seat trader tree、双 512-node book。持久结构只住在账户 bytes 里。",
      en: "Phoenix-v1 profile. 128-seat trader tree, dual 512-node books. Persistent structure lives in account bytes only.",
    },
    lean: `namespace Examples.PhoenixV1Profile

-- Persistent trees are account-resident.
-- Slot 0 is sentinel; no heap Map, no copied tree.

@[pf_entry]
def reduceOrderWithFreeFunds
    (m : Market) (trader : Seat) (side : Side) (qty : Lots) :
    Except Error (Market × Fill) :=
  -- bounded Sokoban insert/remove on the book
  AccountStorage.call m.book (.reduce trader side qty)
`,
    theorems: [
      {
        name: "no_heap_in_account",
        claim: {
          zh: "账户 bytes 不保存 heap 指针。",
          en: "Account bytes never store a heap pointer.",
        },
      },
    ],
    svm: {
      asm: `; Phoenix tag 6/7 FifoCancel — component-owned
  call pf_component_query        ; trader/bid/ask validator
  call pf_fifo_cancel            ; bids → asks, in-place
  ; owner filter, collateral unlock, event index
  ; stay inside the component; no Ops/IR leak`,
      idl: `{ "name": "PhoenixV1Profile", "notes": "Loader-v3 + Surfpool; not solana-test-validator" }`,
    },
  },
];

export function exampleById(id: string): Example | undefined {
  return EXAMPLES.find((e) => e.id === id);
}
