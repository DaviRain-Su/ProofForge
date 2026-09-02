import Lake
open Lake DSL

package «proofforge» where
  version := v!"0.0.1"

require solanalib from git
  "https://github.com/solana-foundation/leanprover-solanalib.git" @
  "6c115ef1ef6a0cde8dbd6fd875b7dc87d60939ec"

require sbpfSemantics from git
  "https://github.com/DaviRain-Su/assembler-semantics.git" @ "64770b7a68c735f5ff6eea73f0d322daf34d7cad"

/-- Shared Attr + Core/Crypto surface used by every target SDK. -/
lean_lib ProofForgeCore where
  roots := #[
    `ProofForge.Attr,
    `ProofForge.Core.Codec,
    `ProofForge.Core.Collections,
    `ProofForge.Core.Math,
    `ProofForge.Core.Ops,
    `ProofForge.Core.SafeCast,
    `ProofForge.Core.Value
  ]

/-- Contract-facing SVM SDK (+ Runtime/Source needed for `pf_inline` erase). No Emit. -/
lean_lib ProofForgeSvmSdk where
  roots := #[
    `ProofForge.Svm.AccountStorage,
    `ProofForge.Svm.AccountStorage.Source,
    `ProofForge.Svm.AccountView,
    `ProofForge.Svm.Cpi.TokenTlv,
    `ProofForge.Svm.Heap,
    `ProofForge.Svm.Memo,
    `ProofForge.Svm.Memory,
    `ProofForge.Svm.Runtime,
    `ProofForge.Svm.Scratch,
    `ProofForge.Svm.Sdk,
    `ProofForge.Svm.Sdk.Account,
    `ProofForge.Svm.Sdk.AssociatedToken,
    `ProofForge.Svm.Sdk.Memo,
    `ProofForge.Svm.Sdk.Memory,
    `ProofForge.Svm.Sdk.Pda,
    `ProofForge.Svm.Sdk.Program,
    `ProofForge.Svm.Sdk.Pubkey,
    `ProofForge.Svm.Sdk.Queue,
    `ProofForge.Svm.Sdk.Storage,
    `ProofForge.Svm.Sdk.StorageBitSet,
    `ProofForge.Svm.Sdk.StorageEnumerableSet,
    `ProofForge.Svm.Sdk.System,
    `ProofForge.Svm.Sdk.Sysvar,
    `ProofForge.Svm.Sdk.Telemetry,
    `ProofForge.Svm.Sdk.Token,
    `ProofForge.Svm.Sdk.Transient,
    `ProofForge.Svm.Sdk.TransientBytes,
    `ProofForge.Svm.Sdk.TransientRecord64,
    `ProofForge.Svm.Sdk.TransientVec,
    `ProofForge.Svm.Sdk.TransientWideVec,
    `ProofForge.Svm.Sdk.Versioned,
    `ProofForge.Svm.Seed,
    `ProofForge.Svm.Telemetry,
    `ProofForge.Svm.TransientBytes,
    `ProofForge.Svm.TransientVec
  ]

/-- Contract-facing EVM SDK (+ Runtime/Source needed for `pf_inline` erase). No Emit. -/
lean_lib ProofForgeEvmSdk where
  roots := #[
    `ProofForge.Evm.ClosedCall.Source,
    `ProofForge.Evm.HashedMap.Source,
    `ProofForge.Evm.NativeFx.Source,
    `ProofForge.Evm.Runtime,
    `ProofForge.Evm.Sdk,
    `ProofForge.Evm.Sdk.Access,
    `ProofForge.Evm.Sdk.Base,
    `ProofForge.Evm.Sdk.Erc1155,
    `ProofForge.Evm.Sdk.Erc721,
    `ProofForge.Evm.Sdk.Fungible,
    `ProofForge.Evm.Sdk.Pausable,
    `ProofForge.Evm.Sdk.Payments,
    `ProofForge.Evm.Sdk.Reentrancy,
    `ProofForge.Evm.Sdk.Roles,
    `ProofForge.Evm.Sdk.Storage,
    `ProofForge.Evm.Sdk.StorageBitmap,
    `ProofForge.Evm.Sdk.StorageCheckpoints,
    `ProofForge.Evm.Sdk.StorageEnumerableMap,
    `ProofForge.Evm.Sdk.StorageEnumerableSet,
    `ProofForge.Evm.Sdk.StorageRing,
    `ProofForge.Evm.Sdk.StorageVec,
    `ProofForge.Evm.StaticStorage.Source,
    `ProofForge.Evm.WideWord.Source
  ]

/-- Compiler, Emit/Assemble/Registry, Wasm targets, and the `ProofForge` umbrella.
This `lean_lib` is the in-repo compiler workspace (prod-002 `ProofForgeCompiler` role).
User templates must depend on `ProofForgeSvmSdk` / `ProofForgeEvmSdk` only. -/
@[default_target]
lean_lib ProofForge where
  roots := #[
    `ProofForge,
    `ProofForge.Cli,
    `ProofForge.Core.CFG,
    `ProofForge.Core.Eval,
    `ProofForge.Core.FixedPoint,
    `ProofForge.Core.IR,
    `ProofForge.Core.Schema,
    `ProofForge.Core.Target,
    `ProofForge.Crypto.Keccak,
    `ProofForge.Crypto.Sha256,
    `ProofForge.Crypto.Sha256Compat,
    `ProofForge.Evm.Assemble,
    `ProofForge.Evm.AssembleMain,
    `ProofForge.Evm.CallResult,
    `ProofForge.Evm.CallResult.Emit,
    `ProofForge.Evm.ClosedCall,
    `ProofForge.Evm.ClosedCall.Emit,
    `ProofForge.Evm.Codec,
    `ProofForge.Evm.Codec.Emit,
    `ProofForge.Evm.Commands,
    `ProofForge.Evm.Component,
    `ProofForge.Evm.Component.Emit,
    `ProofForge.Evm.Emit,
    `ProofForge.Evm.Environment,
    `ProofForge.Evm.Environment.Emit,
    `ProofForge.Evm.Golden,
    `ProofForge.Evm.HashedMap,
    `ProofForge.Evm.HashedMap.Emit,
    `ProofForge.Evm.IR,
    `ProofForge.Evm.IRCompat,
    `ProofForge.Evm.Keccak,
    `ProofForge.Evm.LogError,
    `ProofForge.Evm.LogError.Emit,
    `ProofForge.Evm.NativeFx,
    `ProofForge.Evm.NativeFx.Emit,
    `ProofForge.Evm.Ops,
    `ProofForge.Evm.Payable,
    `ProofForge.Evm.Payable.Emit,
    `ProofForge.Evm.Precompile,
    `ProofForge.Evm.Precompile.Emit,
    `ProofForge.Evm.Registry,
    `ProofForge.Evm.StaticStorage,
    `ProofForge.Evm.StaticStorage.Emit,
    `ProofForge.Evm.WideWord,
    `ProofForge.Evm.WideWord.Emit,
    `ProofForge.Extract,
    `ProofForge.Extract.Compat,
    `ProofForge.Extract.Decode,
    `ProofForge.Extract.IR,
    `ProofForge.Extract.LegacyAdapter,
    `ProofForge.Extract.LegacyEval,
    `ProofForge.Extract.LegacyGolden,
    `ProofForge.Extract.LegacyIR,
    `ProofForge.Extract.LegacyOps,
    `ProofForge.Extract.Lexical,
    `ProofForge.Extract.Ops,
    `ProofForge.Profile,
    `ProofForge.Svm.ABI,
    `ProofForge.Svm.ABICompat,
    `ProofForge.Svm.AccountData,
    `ProofForge.Svm.AccountData.Emit,
    `ProofForge.Svm.AccountStorage.Emit,
    `ProofForge.Svm.AccountView.Emit,
    `ProofForge.Svm.Assemble,
    `ProofForge.Svm.AssembleCompat,
    `ProofForge.Svm.AssembleMain,
    `ProofForge.Svm.BatchRecorder,
    `ProofForge.Svm.BatchRecorder.Emit,
    `ProofForge.Svm.BatchRecorder.Source,
    `ProofForge.Svm.Commands,
    `ProofForge.Svm.Component,
    `ProofForge.Svm.Component.Emit,
    `ProofForge.Svm.Cpi.Emit,
    `ProofForge.Svm.Cpi.TokenTlv.Emit,
    `ProofForge.Svm.Emit,
    `ProofForge.Svm.EmitCompat,
    `ProofForge.Svm.EntryAdapter,
    `ProofForge.Svm.EntryAdapter.Emit,
    `ProofForge.Svm.FifoCancel,
    `ProofForge.Svm.FifoCancel.Emit,
    `ProofForge.Svm.FifoCancel.Source,
    `ProofForge.Svm.Heap.Emit,
    `ProofForge.Svm.IR,
    `ProofForge.Svm.IRCompat,
    `ProofForge.Svm.Idl,
    `ProofForge.Svm.IdlCompat,
    `ProofForge.Svm.Lamports,
    `ProofForge.Svm.Lamports.Emit,
    `ProofForge.Svm.Memory.Emit,
    `ProofForge.Svm.Ops,
    `ProofForge.Svm.Registry,
    `ProofForge.Svm.Sdk.StorageModel,
    `ProofForge.Svm.Semantics,
    `ProofForge.Svm.SemanticsBridge,
    `ProofForge.Svm.Solanalib,
    `ProofForge.Svm.Sysvar,
    `ProofForge.Svm.Sysvar.Emit,
    `ProofForge.Svm.Telemetry.Emit,
    `ProofForge.Svm.Transient.Emit,
    `ProofForge.Svm.TransientBytes.Emit,
    `ProofForge.Svm.TransientVec.Emit,
    `ProofForge.Wasm.Emit,
    `ProofForge.Wasm.Family,
    `ProofForge.Wasm.Host,
    `ProofForge.Wasm.IR,
    `ProofForge.Wasm.Near.Assemble,
    `ProofForge.Wasm.Near.Codec,
    `ProofForge.Wasm.Near.Commands,
    `ProofForge.Wasm.Near.Emit,
    `ProofForge.Wasm.Near.Host,
    `ProofForge.Wasm.Near.IR,
    `ProofForge.Wasm.Near.Memory,
    `ProofForge.Wasm.Near.Ops,
    `ProofForge.Wasm.Near.Registry,
    `ProofForge.Wasm.Near.Runtime,
    `ProofForge.Wasm.Near.Sdk,
    `ProofForge.Wasm.Near.Sdk.Fungible.Ledger,
    `ProofForge.Wasm.Near.Sdk.Fungible.Registration,
    `ProofForge.Wasm.Near.Sdk.Promise,
    `ProofForge.Wasm.Near.Sdk.Storage,
    `ProofForge.Wasm.Near.Sdk.Store.AccountTokenLookup,
    `ProofForge.Wasm.Near.Sdk.Store.Codec,
    `ProofForge.Wasm.Near.Sdk.Store.Iterable,
    `ProofForge.Wasm.Near.Sdk.Store.Lookup,
    `ProofForge.Wasm.Near.Sdk.Store.Queue,
    `ProofForge.Wasm.Near.Sdk.Store.Vector,
    `ProofForge.Wasm.Near.Sdk.Transient,
    `ProofForge.Wasm.Xrpl.Assemble,
    `ProofForge.Wasm.Xrpl.Commands,
    `ProofForge.Wasm.Xrpl.Emit,
    `ProofForge.Wasm.Xrpl.Host,
    `ProofForge.Wasm.Xrpl.IR,
    `ProofForge.Wasm.Xrpl.Ops,
    `ProofForge.Wasm.Xrpl.Registry,
    `ProofForge.Wasm.Xrpl.Runtime,
    `ProofForge.Wasm.Xrpl.Sdk
  ]

/-- Build every module under `Examples/`, including `Examples/{Svm,Evm,Xrpl,Near}/`.
Without `.submodules`, Registry NEAR fixtures (NearQueue/Iterable/Promise/…) never
get oleans from `lake build Examples`, so CI `pf build --target near` fails. -/
lean_lib Examples where
  globs := #[.one `Examples, .submodules `Examples]

lean_lib Tests

lean_exe pfAssemble where
  root := `ProofForge.Svm.AssembleMain

lean_exe pfEvmAssemble where
  root := `ProofForge.Evm.AssembleMain

lean_exe pf where
  root := `ProofForge.Cli
  supportInterpreter := true
