import ProofForge.Evm.Sdk.Base
import ProofForge.Evm.Sdk.Fungible
import ProofForge.Evm.Sdk.Payments
import ProofForge.Evm.Sdk.Pausable
import ProofForge.Evm.Sdk.Access
import ProofForge.Evm.Sdk.Storage
import ProofForge.Evm.Sdk.Roles

/-!
# ProofForge EVM SDK

Contract-facing umbrella for EVM values, typed storage handles, target effects, reusable access /
pause/payment/fungible-ledger policy components, compile-time static storage declarations, and
bounded static role sets. Applications import this module rather than target Runtime, Ops, IR, or
Emit internals.
-/
