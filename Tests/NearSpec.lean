import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx

/-!
# NEAR target tests (WASM family)

v0: registration rejects foreign leaves; digest is pinned; emitted WAT carries
`env` imports and exported entries. Not JSON ABI; not XRPL `host_lib`.
-/

open ProofForge

#guard !ProofForge.Wasm.Near.Ops.Op.wellFormed (.ext .reserved)
#guard !(ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val))
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .reserved == 0

#guard ProofForge.Wasm.Near.Registry.digestOf "Counter" == some "121a0c8f7e697642"
#guard ProofForge.Wasm.Near.Registry.names ==
  #["Counter", "NearCtx", "NearBytes", "NearFungibleTokenEvent", "NearFungibleLedger", "NearTokenArithmetic", "NearTokenStorage", "NearMemory", "NearOutput", "NearStorage", "NearStorageEconomics", "NearStorageRegistration", "NearVector",
    "NearLookup", "NearQueue", "NearIterable", "NearPromise", "NearPromiseResult", "NearMigration"]
#guard ProofForge.Wasm.Near.Registry.digestOf "NearTokenArithmetic" == some "f85fa4f3182ec1eb"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleLedger" == some "b91759b7d8a8fac7"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearTokenStorage" == some "92e4c2bf2a7f74a0"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearCtx" == some "8233f27ab39f6133"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearMemory" == some "830255873ad66d7c"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearOutput" == some "aef385d73b807e1f"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorage" == some "cd97bb762dac8be3"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageEconomics" == some "9c98eca433f99470"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageRegistration" == some "92f4f04bdcaeff81"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearVector" == some "cd60fb0f3ce40ade"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearLookup" == some "d14778ca02c69012"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearQueue" == some "a8bf10c3476ef45f"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearIterable" == some "98d132f8e2c7cd5c"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearPromise" == some "6980479348d2eca3"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearPromiseResult" == some "7f65ba128b01a035"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearMigration" == some "19a760409263b854"

#guard ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.logUtf8 "NEAR ✓" : ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val)
#guard !ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.logUtf8 (String.ofList (List.replicate 1025 'x')) :
    ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val)

open Lean Elab Command in
elab "#pf_near_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .ok _ => throwError "expected near to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "near rejects" do
        throwError "unexpected near rejection reason: {reason}"

#pf_near_reject Examples.Clock

#pf_near_reject Examples.EvmCtx

#pf_near_build Examples.Counter

open Lean Elab Command in
elab "#pf_near_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let digest := ProofForge.Wasm.Near.IR.digestHex program
        let uninitializedGuard :=
          "(if (i64.eq (call $pf_storage_read (i64.const 5) (i64.const 2096) " ++
            "(i64.const 5)) (i64.const 0))"
        let uninitializedPanic :=
          "(call $pf_panic_utf8 (i64.const 31) (i64.const 12288))"
        let uninitializedData :=
          "(data (i32.const 12288) \"\\54\\68\\65\\20\\63\\6f\\6e\\74\\72\\61" ++
            "\\63\\74\\20\\69\\73\\20\\6e\\6f\\74\\20\\69\\6e\\69\\74" ++
            "\\69\\61\\6c\\69\\7a\\65\\64\")"
        let schemaCanonical := ProofForge.Wasm.Near.IR.stateSchemaCanonical program
        let schemaDigest := ProofForge.Wasm.Near.IR.stateSchemaDigest program
        unless schemaCanonical == "near-state-schema-v1|1|5:value:8:6:u64-le" &&
            schemaDigest == (0x8de0fef1e13b14ad : UInt64) do
          throwError s!"unexpected Counter state schema identity: {schemaCanonical} / {schemaDigest}"
        let logicUpgrade := { program with entries := program.entries.reverse }
        unless ProofForge.Wasm.Near.IR.stateSchemaDigest logicUpgrade == schemaDigest do
          throwError "method-only upgrade changed the state schema identity"
        let renamedSchema := { program with slots := program.slots.map fun slot =>
          { slot with name := slot.name ++ "2" } }
        unless ProofForge.Wasm.Near.IR.stateSchemaDigest renamedSchema != schemaDigest do
          throwError "renamed state slot preserved the schema identity"
        let widenedSchema := { program with slots := program.slots.map fun slot =>
          { slot with width := slot.width + 8 } }
        let changedAbiSchema := { program with slots := program.slots.map fun slot =>
          { slot with abi := slot.abi ++ ".v2" } }
        unless ProofForge.Wasm.Near.IR.stateSchemaDigest widenedSchema != schemaDigest &&
            ProofForge.Wasm.Near.IR.stateSchemaDigest changedAbiSchema != schemaDigest do
          throwError "physical width/ABI change preserved the state schema identity"
        match ProofForge.Wasm.Near.Registry.digestOf program.name with
        | some want =>
            if digest != want then
              throwError s!"ir/mismatch: extracted near {program.name} digest {digest} != fixture {want}"
        | none => pure ()
        let anchors : Array String := #[
          "(import \"env\" \"input\"",
          "(import \"env\" \"register_len\"",
          "(import \"env\" \"read_register\"",
          "(import \"env\" \"storage_read\"",
          "(import \"env\" \"storage_write\"",
          "(import \"env\" \"value_return\"",
          "(import \"env\" \"panic_utf8\"",
          "(import \"env\" \"attached_deposit\"",
          "(data (i32.const 2096) \"STATE\")",
          "(data (i32.const 2101) \"The contract has already been initialized\")",
          uninitializedData,
          "(func (export \"initialize\")",
          "(func (export \"increment\")",
          "(func (export \"get\")",
          "(func (export \"nonzero\")",
          "i64.add",
          "i64.sub",
          "i64.mul",
          "i64.div_u",
          "i64.rem_u",
          "call $pf_storage_read",
          "(call $pf_storage_has_key (i64.const 5) (i64.const 2096))",
          "(call $pf_storage_has_key (i64.const 5) (i64.const 1024))",
          "call $pf_storage_write",
          "call $pf_value_return"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"near emit is missing anchor: {anchor}\n{source}"
        unless (source.splitOn uninitializedData).length == 2 do
          throwError "near emit must deduplicate the exact uninitialized panic data"
        unless !source.contains "host_lib" do
          throwError "near emit mentions XRPL host_lib"
        unless !source.contains "\"log_utf8\"" do
          throwError "Counter unexpectedly imports NEAR log_utf8"
        unless !source.contains "xrpl_wasm_std" do
          throwError "near emit still mentions xrpl_wasm_std"
        let initializeBody ← match source.splitOn "(func (export \"initialize\")" with
          | [_prefix, suffix] => pure ((suffix.splitOn "\n  (func (export").headD "")
          | _ => throwError "near emit must contain exactly one initializer wrapper"
        let afterDepositGuard ← match initializeBody.splitOn
            "(call $pf_attached_deposit (i64.const 24))" with
          | [before, after] =>
              unless !before.contains "(call $pf_input" do
                throwError "initializer decoded input before enforcing non-payable policy"
              unless after.contains "(i64.load (i32.const 24))" &&
                  after.contains "(i64.load (i32.const 32))" do
                throwError "initializer non-payable guard did not inspect the full u128 deposit"
              pure after
          | _ => throwError "initializer must read attached deposit exactly once"
        unless afterDepositGuard.contains "(call $pf_panic_utf8 (i64.const 40)" do
          throwError "initializer lost its exact method-specific non-payable panic"
        let afterStateGuard ← match initializeBody.splitOn
            "(call $pf_storage_has_key (i64.const 5) (i64.const 2096))" with
          | [before, after] =>
              unless before.contains "(local.set $pf_p0 (i64.load (i32.const 0)))" do
                throwError "initializer consulted STATE before decoding its argument"
              pure after
          | _ => throwError "initializer must check the reserved STATE marker exactly once"
        if initializeBody.contains uninitializedGuard then
          throwError "initializer received the ordinary missing-STATE guard"
        let afterLegacyGuard ← match afterStateGuard.splitOn
            "(call $pf_storage_has_key (i64.const 5) (i64.const 1024))" with
          | [_before, after] => pure after
          | _ => throwError "initializer must check its legacy scalar slot after STATE"
        let afterStateStore ← match afterLegacyGuard.splitOn
            ("(call $pf_storage_write (i64.const 5) (i64.const 2096) (i64.const 16) " ++
              "(i64.const 192)") with
          | [before, after] =>
              unless before.contains
                  "(call $pf_storage_write (i64.const 5) (i64.const 1024) (i64.const 8)" &&
                  before.contains
                    "(i64.store (i32.const 192) (i64.const 3544425623580460624))" &&
                  before.contains
                    "(i64.store (i32.const 200) (i64.const 10223451468950344877))" do
                throwError "initializer marked STATE before persisting its scalar state"
              pure after
          | _ => throwError "initializer must write the STATE marker exactly once"
        unless !afterStateStore.contains "(call $pf_storage_write (i64.const 5) (i64.const 2096)" do
          throwError "initializer wrote the STATE marker more than once"
        unless (source.splitOn
            "(call $pf_storage_write (i64.const 5) (i64.const 2096) (i64.const 16)").length == 2 do
          throwError "STATE marker write must occur exactly once in the whole module"
        match ProofForge.Wasm.Near.Emit.emit {
            program with initializer := {
              program.initializer with ops := #[.returnU64 (.lit 0)] } } with
        | .error reason =>
            unless reason.contains "near initializer must return state" do
              throwError s!"unexpected scalar initializer rejection: {reason}"
        | .ok _ => throwError "scalar-return initializer bypassed STATE marker persistence"
        let getBody ← match source.splitOn "(func (export \"get\")" with
          | [_prefix, suffix] => pure ((suffix.splitOn "\n  (func (export").headD "")
          | _ => throwError "near emit must contain exactly one get view"
        unless !getBody.contains "(call $pf_attached_deposit" do
          throwError "near view unexpectedly received a non-payable deposit guard"
        for method in program.entries do
          let body ← match source.splitOn ("(func (export \"" ++ method.ixName ++ "\")") with
            | [_prefix, suffix] => pure ((suffix.splitOn "\n  (func (export").headD "")
            | _ => throwError s!"near emit must contain exactly one {method.ixName} wrapper"
          match body.splitOn uninitializedGuard with
          | [before, after] =>
              unless before.contains "(call $pf_input" do
                throwError s!"{method.ixName} checked STATE before input decoding"
              unless after.contains uninitializedPanic do
                throwError s!"{method.ixName} lost the exact uninitialized panic"
              unless after.contains "(call $pf_register_len (i64.const 5)) (i64.const 16)" &&
                  after.contains "(i64.load (i32.const 192)) " &&
                  after.contains "(i64.load (i32.const 200)) " &&
                  after.contains "(call $pf_panic_utf8 (i64.const 42) (i64.const 12319))" do
                throwError s!"{method.ixName} lost STATE length/version/schema validation"
              match after.splitOn "(call $pf_storage_read" with
              | [beforeRead, _afterRead] =>
                  unless beforeRead.contains uninitializedPanic do
                    throwError s!"{method.ixName} read scalar state before its STATE guard"
              | _ => throwError s!"{method.ixName} must read its scalar state exactly once"
          | _ => throwError s!"{method.ixName} must check STATE existence exactly once"
        logInfo m!"proofforge-near-test: digest = {digest}"
        logInfo m!"proofforge-near-test: {source.length} bytes of WAT passed anchor check"

#pf_near_emit_check Examples.Counter
