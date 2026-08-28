import ProofForge.Attr
import ProofForge.Evm.Runtime

namespace ProofForge.Evm.StaticStorage.Source

/--
Immediately store one UInt64 static field in lexical effect order. `field` must reduce to a
compiler-static name and is resolved against the extracted contract schema; applications normally
obtain it through `Sdk.Storage.Static.Handle.storeNow` rather than spelling a name.
-/
@[pf_inline] def storeU64 (field : String) (value : UInt64) : UInt64 :=
  Runtime.evmStoreStaticU64 field value

end ProofForge.Evm.StaticStorage.Source
