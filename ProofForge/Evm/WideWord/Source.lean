import ProofForge.Attr
import ProofForge.Evm.Runtime

namespace ProofForge.Evm.WideWord.Source

open ProofForge.Evm.Runtime

/--
Source-facing packed 256-bit / Addr20 operations. `@[pf_inline]` erases these helpers into the
existing Runtime stubs and `Evm.WideWord` component queries. No new Ops, IR, or main-emitter
case is introduced.
-/

@[pf_inline] def add256 (a b : UInt256) : UInt256 :=
  evmAdd256 a b

@[pf_inline] def sub256 (a b : UInt256) : UInt256 :=
  evmSub256 a b

@[pf_inline] def mul256 (a b : UInt256) : UInt256 :=
  evmMul256 a b

@[pf_inline] def ge256 (a b : UInt256) : Bool :=
  evmGe256 a b

@[pf_inline] def eq20 (a b : Addr20) : Bool :=
  evmEq20 a b

end ProofForge.Evm.WideWord.Source
