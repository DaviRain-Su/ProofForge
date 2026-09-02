import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Near.NearFungibleTokenEvent

/-!
# Exact NEP-141 fungible-token events

This pins mint/transfer/burn event serialization only: complete AccountId staging, JSON escaping,
full-u128 decimal, official field order, optional bounded memo variants, and one compact
`EVENT_JSON:` log. It is not an FT state/method implementation.
-/

open ProofForge
open Lean Elab Command

private def amountOf (method : ProofForge.Wasm.Near.IR.Method) : Option (UInt64 × UInt64) :=
  method.ops.findSome? fun
    | .ext (.nep141FtMint owner (.lit lo) (.lit hi)) =>
        if owner.size == 9 then some (lo, hi) else none
    | _ => none

private def hasExpectedTransfer (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  method.ops.any fun
    | .ext (.nep141FtTransfer oldOwner newOwner (.lit lo) (.lit hi)) =>
        oldOwner.size == 9 && newOwner.size == 9 &&
          lo == 18446744073709551615 && hi == 18446744073709551615
    | _ => false

private def hasExpectedBurn (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  method.ops.any fun
    | .ext (.nep141FtBurn owner (.lit lo) (.lit hi)) =>
        owner.size == 9 && lo == 0 && hi == 1
    | _ => false

private def hasExpectedMintMemo (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  method.ops.any fun
    | .ext (.nep141FtMintMemo capacity owner (.lit lo) (.lit hi) memo) =>
        capacity == 16 && owner.size == 9 && lo == 0 && hi == 0 && memo.size == 17
    | _ => false

private def hasExpectedTransferMemo (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  method.ops.any fun
    | .ext (.nep141FtTransferMemo capacity oldOwner newOwner (.lit lo) (.lit hi) memo) =>
        capacity == 16 && oldOwner.size == 9 && newOwner.size == 9 &&
          lo == 1 && hi == 1 && memo.size == 17
    | _ => false

private def hasExpectedBurnMemo (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  method.ops.any fun
    | .ext (.nep141FtBurnMemo capacity owner (.lit lo) (.lit hi) memo) =>
        capacity == 16 && owner.size == 9 && lo == 18446744073709551615 &&
          hi == 18446744073709551615 && memo.size == 17
    | _ => false

elab "#pf_guard_near_ft_events" : command => do
  let env ← getEnv
  let extracted ←
    match Extract.extractModuleIR env `Examples.Near.NearFungibleTokenEvent none with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted extracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let expected : Array (String × UInt64 × UInt64) := #[
    ("mintZero", 0, 0),
    ("mintTwo64", 0, 1),
    ("mintTwo64PlusOne", 1, 1),
    ("mintMax", 18446744073709551615, 18446744073709551615)
  ]
  for (name, lo, hi) in expected do
    let some method := program.entries.find? (·.ixName == name)
      | throwError s!"missing {name}"
    unless amountOf method == some (lo, hi) do
      throwError s!"wrong {name} ft_mint payload: " ++
        ProofForge.Wasm.IR.opsCanon ProofForge.Wasm.Near.IR.extValCanon
          ProofForge.Wasm.Near.IR.extOpCanon method.ops
  let some (transfer : ProofForge.Wasm.Near.IR.Method) :=
      program.entries.find? (·.ixName == "transferMax")
    | throwError "missing transferMax"
  unless hasExpectedTransfer transfer do
    let canon := ProofForge.Wasm.IR.opsCanon ProofForge.Wasm.Near.IR.extValCanon
      ProofForge.Wasm.Near.IR.extOpCanon transfer.ops
    throwError s!"wrong transferMax ft_transfer payload: {canon}"
  let some (burn : ProofForge.Wasm.Near.IR.Method) :=
      program.entries.find? (·.ixName == "burnTwo64")
    | throwError "missing burnTwo64"
  unless hasExpectedBurn burn do
    let canon := ProofForge.Wasm.IR.opsCanon ProofForge.Wasm.Near.IR.extValCanon
      ProofForge.Wasm.Near.IR.extOpCanon burn.ops
    throwError s!"wrong burnTwo64 ft_burn payload: {canon}"
  let memoExpected : Array (String × (ProofForge.Wasm.Near.IR.Method → Bool)) := #[
    ("mintMemo", hasExpectedMintMemo),
    ("transferMemo", hasExpectedTransferMemo),
    ("burnMemo", hasExpectedBurnMemo)
  ]
  for (name, predicate) in memoExpected do
    let some method := program.entries.find? (·.ixName == name)
      | throwError s!"missing {name}"
    unless predicate method do
      let canon := ProofForge.Wasm.IR.opsCanon ProofForge.Wasm.Near.IR.extValCanon
        ProofForge.Wasm.Near.IR.extOpCanon method.ops
      throwError s!"wrong {name} bounded memo payload: {canon}"
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok source => pure source
    | .error reason => throwError reason
  let anchors : Array String := #[
    "(func $pf_json_escape_byte",
    "(func $pf_u128_decimal",
    "(local.set $bit (i64.const 128))",
    "(local.set $i (i64.const 0))",
    "(i64.const 39)",
    "(br $digits_loop)",
    "(local.set $i (i64.const 39))",
    "(br $output)",
    "(call $pf_arena_alloc (i64.const 528) (i64.const 1))",
    "(call $pf_arena_alloc (i64.const 938) (i64.const 1))",
    "(call $pf_arena_alloc (i64.const 634) (i64.const 1))",
    "(call $pf_arena_alloc (i64.const 1044) (i64.const 1))",
    "(call $pf_arena_alloc (i64.const 39) (i64.const 1))",
    "(call $pf_json_escape_byte",
    "(call $pf_u128_decimal",
    "(func (export \"mintZero\")",
    "(func (export \"mintTwo64\")",
    "(func (export \"mintTwo64PlusOne\")",
    "(func (export \"mintMax\")",
    "(func (export \"transferMax\")",
    "(func (export \"burnTwo64\")",
    "(func (export \"mintMemo\")",
    "(func (export \"transferMemo\")",
    "(func (export \"burnMemo\")",
    "(i64.const 16)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEP-141 event WAT is missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-ft-event-test: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_ft_events
#pf_near_build Examples.Near.NearFungibleTokenEvent

#guard ProofForge.Wasm.Near.Codec.nep141MemoCapacityValid 16
#guard !ProofForge.Wasm.Near.Codec.nep141MemoCapacityValid 17

#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleTokenEvent" ==
  some "768db0d9cec95f94"
