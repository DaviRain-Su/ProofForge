import ProofForge.Core.SafeCast
import ProofForge.Evm.Sdk.Base
import ProofForge.Evm.Sdk.Fungible
import ProofForge.Evm.Sdk.Erc721
import ProofForge.Evm.Sdk.Erc1155
import ProofForge.Evm.Sdk.Payments
import ProofForge.Evm.Sdk.Pausable
import ProofForge.Evm.Sdk.Access
import ProofForge.Evm.Sdk.Storage
import ProofForge.Evm.Sdk.StorageVec
import ProofForge.Evm.Sdk.StorageBitmap
import ProofForge.Evm.Sdk.StorageRing
import ProofForge.Evm.Sdk.StorageEnumerableSet
import ProofForge.Evm.Sdk.StorageEnumerableMap
import ProofForge.Evm.Sdk.StorageCheckpoints
import ProofForge.Evm.Sdk.Roles
import ProofForge.Evm.Sdk.Reentrancy

/-!
# ProofForge EVM SDK

Contract-facing umbrella for EVM values, typed storage handles, target effects, reusable access /
pause/reentrancy/payment/fungible/ERC-721/bounded-ERC-1155 ledger policy components, compile-time
static storage declarations, persistent bounded UInt64 storage vectors/bitmaps/ring queues/
enumerable sets/maps/checkpoints, bounded static role sets, and shared allocation-free checked
wide-to-UInt8/UInt16/UInt32/UInt64 narrowing. Applications import this module rather than target
Runtime, Ops, IR, or Emit internals.
-/
