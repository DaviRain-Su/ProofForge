import Examples.SelfLog

namespace Tests.SelfLogSpec

open Lean Elab Command
open ProofForge.Svm

#guard Examples.SelfLog.init 7 == { value := 7 }
#guard match Examples.SelfLog.record (Examples.SelfLog.init 0) 42 with
  | .ok (state, value) => state == { value := 42 } && value == 42
  | .error _ => false
#guard Examples.SelfLog.get (Examples.SelfLog.init 42) == 42

elab "#pf_guard_self_log_ir" : command => do
  let env ← getEnv
  let extracted ←
    match ProofForge.Extract.extractModuleIR env `Examples.SelfLog with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted extracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let some record := program.methods.find? (·.ixName == "record")
    | throwError "missing record method"
  let expected : Array IR.Op := #[
    .invoke 1
      #[{ acc := 0, signer := true, writable := false }]
      #[.selfEntry 15 "log", .u16le (.arg 0), .u64le (.arg 0)]
      #[.ascii "log"] (some (.ext (.findPda "log") #[])),
    .storeField "value" (.arg 0),
    .okState (.arg 0)
  ]
  unless record.ops == expected do
    throwError s!"raw self-entry IR mismatch: {repr record.ops}"
  match IR.rawSelfEntry? program with
  | .ok (some entry) =>
      unless entry.tag == 15 && entry.authoritySeed == "log" do
        throwError s!"wrong raw self-entry declaration: {repr entry}"
  | result => throwError s!"raw self-entry declaration was not retained: {repr result}"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "jeq r1, 1, raw_self_entry" &&
      asm.contains "signed raw self-entry tag=15 seed=log" &&
      asm.contains "raw self-entry invocations use the current program id" &&
      asm.contains "call sol_try_find_program_address" &&
      asm.contains "call sol_invoke_signed_c" &&
      asm.contains "stxh" && asm.contains "stxdw" do
    throwError "raw self-entry assembly contract is incomplete"

#pf_guard_self_log_ir

private def invocation (tag : UInt64 := 15) (authoritySeed : String := "log")
    (metas : Array Ops.CpiMeta := #[{ acc := 0, signer := true }])
    (seeds : Array Ops.PdaSeed := #[.ascii "log"])
    (bump : Option Ops.Val := some (.lit 1)) : IR.Op :=
  .invoke 1 metas #[.selfEntry tag authoritySeed] seeds bump

private def rawProgram (ops : Array IR.Op) : IR.Program :=
  { name := "RawSelfFixture"
    slots := #[{ name := "value", offset := 8, width := 8, abi := "u64-le" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "record", ixName := "record", ops },
      { kind := .get, name := "get", ixName := "get", ops := #[.returnU64 (.lit 0)] }
    ] }

private def accepted : Except String α → Bool
  | .ok _ => true
  | .error _ => false

#guard accepted (IR.rawSelfEntry? (rawProgram #[invocation]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[invocation (metas := #[])]))
#guard !accepted (IR.rawSelfEntry? (rawProgram
  #[invocation (metas := #[{ acc := 0, signer := false }])]))
#guard !accepted (IR.rawSelfEntry? (rawProgram
  #[invocation (metas := #[{ acc := 0, signer := true, writable := true }])]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[invocation (seeds := #[.ascii "other"])]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[invocation (bump := none)]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[.invoke 1
  #[{ acc := 0, signer := true }]
  #[.u8le (.lit 1), .selfEntry 15 "log"]
  #[.ascii "log"] (some (.lit 1))]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[invocation 15 "log", invocation 16 "log"]))
#guard !accepted (IR.rawSelfEntry? (rawProgram #[invocation 15 "log", invocation 15 "audit"]))

end Tests.SelfLogSpec
