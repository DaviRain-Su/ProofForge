import ProofForge.Svm.Ops
import ProofForge.Evm.Ops

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

end Tests.TargetOpsSpec
