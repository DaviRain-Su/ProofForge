import ProofForge
import Examples.Svm.Phoenix
import Examples.Svm.PhoenixV1Profile

/-!
# Phoenix build gates (phoenix lane)

Phoenix extract/emit digest gates and Phoenix SDK-descriptor guards, moved out of
`Tests.BuildSpec` / `Tests.SvmSdkTokenSpec` so the main `Tests` library no longer
builds the Phoenix application surface. Built by the `PhoenixTests` lake target
(phoenix CI lane), not by `lake build Tests`.
-/

#pf_build Examples.Svm.Phoenix

#pf_build Examples.Svm.PhoenixV1Profile

-- Token/CPI account descriptors used by the official profile (moved from SvmSdkTokenSpec).
#guard Examples.Svm.Phoenix.baseDepositTokenAccounts.wellFormed
#guard Examples.Svm.Phoenix.quoteDepositTokenAccounts.wellFormed
#guard Examples.Svm.Phoenix.baseWithdrawTokenAccounts.wellFormed
#guard Examples.Svm.Phoenix.quoteWithdrawTokenAccounts.wellFormed
#guard Examples.Svm.PhoenixV1Profile.baseWithdrawTokenAccounts.wellFormed
#guard Examples.Svm.PhoenixV1Profile.quoteWithdrawTokenAccounts.wellFormed
