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

/-- Limb reads of packed arith. Contracts writing a `UInt256` state field name these instead of
projecting `UInt256.wN (add256 …)`, so Extract does not flatten the projection into a schema leaf. -/
@[pf_inline] def addW0 (a b : UInt256) : UInt64 := (evmAdd256 a b).w0
@[pf_inline] def addW1 (a b : UInt256) : UInt64 := (evmAdd256 a b).w1
@[pf_inline] def addW2 (a b : UInt256) : UInt64 := (evmAdd256 a b).w2
@[pf_inline] def addW3 (a b : UInt256) : UInt64 := (evmAdd256 a b).w3

@[pf_inline] def subW0 (a b : UInt256) : UInt64 := (evmSub256 a b).w0
@[pf_inline] def subW1 (a b : UInt256) : UInt64 := (evmSub256 a b).w1
@[pf_inline] def subW2 (a b : UInt256) : UInt64 := (evmSub256 a b).w2
@[pf_inline] def subW3 (a b : UInt256) : UInt64 := (evmSub256 a b).w3

@[pf_inline] def mulW0 (a b : UInt256) : UInt64 := (evmMul256 a b).w0
@[pf_inline] def mulW1 (a b : UInt256) : UInt64 := (evmMul256 a b).w1
@[pf_inline] def mulW2 (a b : UInt256) : UInt64 := (evmMul256 a b).w2
@[pf_inline] def mulW3 (a b : UInt256) : UInt64 := (evmMul256 a b).w3

@[pf_inline] def add (a b : UInt256) : UInt256 :=
  ⟨addW0 a b, addW1 a b, addW2 a b, addW3 a b⟩

@[pf_inline] def sub (a b : UInt256) : UInt256 :=
  ⟨subW0 a b, subW1 a b, subW2 a b, subW3 a b⟩

@[pf_inline] def mul (a b : UInt256) : UInt256 :=
  ⟨mulW0 a b, mulW1 a b, mulW2 a b, mulW3 a b⟩

@[pf_inline] def ge256 (a b : UInt256) : Bool :=
  evmGe256 a b

@[pf_inline] def eq256 (a b : UInt256) : Bool :=
  evmEq256 a b

@[pf_inline] def lt256 (a b : UInt256) : Bool :=
  evmLt256 a b

@[pf_inline] def le256 (a b : UInt256) : Bool :=
  evmLe256 a b

@[pf_inline] def gt256 (a b : UInt256) : Bool :=
  evmGt256 a b

@[pf_inline] def eq20 (a b : Addr20) : Bool :=
  evmEq20 a b

@[pf_inline] def zero20 : Addr20 := ⟨0, 0, 0⟩

@[pf_inline] def isZero20 (a : Addr20) : Bool :=
  eq20 a zero20

@[pf_inline] def eqImm20 (a : Addr20) : Bool :=
  eq20 a evmImm20

end ProofForge.Evm.WideWord.Source
