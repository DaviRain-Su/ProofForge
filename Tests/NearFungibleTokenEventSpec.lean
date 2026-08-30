import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.NearFungibleTokenEvent

/-!
# Exact no-memo NEP-141 ft_mint event

This pins event serialization only: complete AccountId staging, JSON escaping, full-u128 decimal,
and one compact `EVENT_JSON:` log. It is not an FT state/method implementation.
-/

open ProofForge
open Lean Elab Command

private def amountOf (method : ProofForge.Wasm.Near.IR.Method) : Option (UInt64 × UInt64) :=
  method.ops.findSome? fun
    | .ext (.nep141FtMint owner (.lit lo) (.lit hi)) =>
        if owner.size == 9 then some (lo, hi) else none
    | _ => none

elab "#pf_guard_near_ft_mint_event" : command => do
  let env ← getEnv
  let extracted ←
    match Extract.extractModuleIR env `Examples.NearFungibleTokenEvent none with
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
    "(call $pf_arena_alloc (i64.const 39) (i64.const 1))",
    "(call $pf_json_escape_byte",
    "(call $pf_u128_decimal",
    "(func (export \"mintZero\")",
    "(func (export \"mintTwo64\")",
    "(func (export \"mintTwo64PlusOne\")",
    "(func (export \"mintMax\")"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEP-141 ft_mint WAT is missing {anchor}\n{wat}"
  if wat.contains "\"memo\"" then
    throwError "NEP-141 ft_mint unexpectedly serialized memo"
  logInfo m!"proofforge-near-ft-event-test: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_ft_mint_event
#pf_near_build Examples.NearFungibleTokenEvent

#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleTokenEvent" ==
  some "f722b151ce6ec284"
