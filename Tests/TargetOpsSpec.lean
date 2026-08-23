import ProofForge.Svm.Ops
import ProofForge.Evm.Ops
import ProofForge.Extract.IR
import ProofForge.Golden

namespace Tests.TargetOpsSpec

private def validSvmValue : ProofForge.Svm.Ops.Val :=
  ProofForge.Svm.Ops.checkPda "vault" (ProofForge.Svm.Ops.findPda "vault")

private def invalidSvmValue : ProofForge.Svm.Ops.Val :=
  .ext (.checkPda "vault") #[]

#guard validSvmValue.wellFormed ProofForge.Svm.Ops.ValKind.arity
#guard !invalidSvmValue.wellFormed ProofForge.Svm.Ops.ValKind.arity

private def validSvmOp : ProofForge.Svm.Ops.Op :=
  .ext (.invoke 2
    #[{ acc := 0, signer := true, writable := true }]
    #[.u64le validSvmValue]
    (some "vault")
    (some validSvmValue))

#guard validSvmOp.wellFormed

private def validEvmValue : ProofForge.Evm.Ops.Val :=
  ProofForge.Evm.Ops.mapGetU64 ProofForge.Evm.Ops.self (.lit 7)

private def invalidEvmValue : ProofForge.Evm.Ops.Val :=
  .ext .mapGetU64 #[ProofForge.Evm.Ops.self]

#guard validEvmValue.wellFormed ProofForge.Evm.Ops.ValKind.arity
#guard !invalidEvmValue.wellFormed ProofForge.Evm.Ops.ValKind.arity

private def validEvmOp : ProofForge.Evm.Ops.Op :=
  .ext (.sendEth (.lit 1) (.lit 2) (.lit 3) validEvmValue)

#guard validEvmOp.wellFormed

private def legacyOpsRoundTrip (ops : Array ProofForge.Ops.Op) : Bool :=
  let extensible := ProofForge.Extract.IR.ofLegacyOps ops
  extensible.all ProofForge.Extract.IR.Op.wellFormed &&
    match ProofForge.Extract.IR.toLegacyOps extensible with
    | .ok restored => restored == ops
    | .error _ => false

#guard ProofForge.Golden.programs.all fun program =>
  program.methods.all fun method => legacyOpsRoundTrip method.ops

#guard ProofForge.Golden.programs.all fun program =>
  match ProofForge.Extract.IR.ofLegacyProgram program >>= ProofForge.Extract.IR.toLegacyProgram with
  | .ok restored => restored == program
  | .error _ => false

private def coreSchema : ProofForge.Core.Schema :=
  { rootType := "CoreCounter.State"
    leaves := #[{
      place := { steps := #[.field "CoreCounter.State" 0 "value"] }
      name := "value"
      ty := .uint 64
    }] }

private def coreProgram : ProofForge.Extract.IR.Program :=
  let schema := coreSchema
  { name := "CoreCounter"
    slots := ProofForge.Core.IR.slotsOfSchema schema
    schema
    methods := #[
      { kind := .init, name := "init", ixName := "initialize" },
      { kind := .increment, name := "tick", ixName := "tick" },
      { kind := .get, name := "get", ixName := "get" }
    ] }

#guard ProofForge.Core.IR.schemaMatchesSlots coreProgram
#guard ProofForge.Core.IR.isProgramShape coreProgram

private def genericEvaluation : Except String ProofForge.Extract.IR.Evaluation :=
  let slot : ProofForge.Extract.IR.Val := .ext (.svm .clockSlot) #[]
  let ops : Array ProofForge.Extract.IR.Op :=
    #[.storeField "value" slot, .okState slot]
  ProofForge.Core.evaluate coreSchema ops

#guard
  match genericEvaluation with
  | .ok evaluation =>
      evaluation.explicit && evaluation.events.size == 2 &&
        evaluation.commits.size == 1 && evaluation.commits[0]!.writes.isEmpty
  | .error _ => false

end Tests.TargetOpsSpec
