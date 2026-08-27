import ProofForge.Attr
import ProofForge.Evm.Runtime
import ProofForge.Evm.WideWord.Source
import ProofForge.Evm.NativeFx.Source

namespace ProofForge.Evm.HashedMap.Source

open ProofForge.Evm.Runtime

/--
Source-facing handles for hashed storage maps. A contract names a static map once and calls these
operations with only dynamic keys and values. `@[pf_inline]` erases the handle at extraction,
leaving the existing hashed-map component plan; no runtime geometry or new EVM operation is
introduced.
-/

structure MapU64 where
  base : UInt64
  deriving BEq, Repr, Inhabited

structure MapAddr where
  base : UInt64
  deriving BEq, Repr, Inhabited

structure MapPair where
  base : UInt64
  deriving BEq, Repr, Inhabited

structure MapAddr256 where
  base : UInt64
  deriving BEq, Repr, Inhabited

structure MapPair256 where
  base : UInt64
  deriving BEq, Repr, Inhabited

attribute [pf_inline]
  MapU64.base MapAddr.base MapPair.base MapAddr256.base MapPair256.base

@[pf_inline] def getU64 (map : MapU64) (key : UInt64) : UInt64 :=
  evmMapGetU64 map.base key

@[pf_inline] def setU64 (map : MapU64) (key value : UInt64) : UInt64 :=
  evmMapSetU64 map.base key value

@[pf_inline] def getAddr (map : MapAddr) (key : Addr20) : UInt64 :=
  evmMapGetAddr map.base key

@[pf_inline] def setAddr (map : MapAddr) (key : Addr20) (value : UInt64) : UInt64 :=
  evmMapSetAddr map.base key value

@[pf_inline] def getPair (map : MapPair) (owner spender : Addr20) : UInt64 :=
  evmMapGetPair map.base owner spender

@[pf_inline] def setPair (map : MapPair) (owner spender : Addr20) (value : UInt64) : UInt64 :=
  evmMapSetPair map.base owner spender value

@[pf_inline] def getAddr256 (map : MapAddr256) (key : Addr20) : UInt256 :=
  evmMapGetAddr256 map.base key

@[pf_inline] def setAddr256 (map : MapAddr256) (key : Addr20) (value : UInt256) : UInt64 :=
  evmMapSetAddr256 map.base key value

@[pf_inline] def getPair256 (map : MapPair256) (owner spender : Addr20) : UInt256 :=
  evmMapGetPair256 map.base owner spender

@[pf_inline] def setPair256 (map : MapPair256) (owner spender : Addr20)
    (value : UInt256) : UInt64 :=
  evmMapSetPair256 map.base owner spender value

/-- Packed comparison against a map slot. Contracts name these instead of
`ge256 (getAddr256 …) amt`. `@[pf_inline]` erases them into the existing WideWord query. -/
@[pf_inline] def geAddr256 (map : MapAddr256) (key : Addr20) (amt : UInt256) : Bool :=
  WideWord.Source.ge256 (getAddr256 map key) amt

@[pf_inline] def gePair256 (map : MapPair256) (owner spender : Addr20)
    (amt : UInt256) : Bool :=
  WideWord.Source.ge256 (getPair256 map owner spender) amt

/-- Next packed value of a map slot. Contracts bind this once and feed the same `UInt256` to
`set*` and LOG, instead of writing `add256 (get …) amt` at each use. `@[pf_inline]` erases
these into the existing WideWord arith queries. They are not writes: packing get+arith+set
into one helper duplicates the arith under LOG and changes extracted IR. -/
@[pf_inline] def nextAddAddr256 (map : MapAddr256) (key : Addr20) (amt : UInt256) : UInt256 :=
  WideWord.Source.add256 (getAddr256 map key) amt

@[pf_inline] def nextSubAddr256 (map : MapAddr256) (key : Addr20) (amt : UInt256) : UInt256 :=
  WideWord.Source.sub256 (getAddr256 map key) amt

@[pf_inline] def nextAddPair256 (map : MapPair256) (owner spender : Addr20)
    (amt : UInt256) : UInt256 :=
  WideWord.Source.add256 (getPair256 map owner spender) amt

@[pf_inline] def nextSubPair256 (map : MapPair256) (owner spender : Addr20)
    (amt : UInt256) : UInt256 :=
  WideWord.Source.sub256 (getPair256 map owner spender) amt

/-- Map-slot Insufficient. Contracts name the handle instead of
`revertInsufficient (getAddr256 …) want`. `@[pf_inline]` erases into NativeFx plus map get. -/
@[pf_inline] def revertInsufficientAddr256 (map : MapAddr256) (key : Addr20)
    (want : UInt256) : UInt64 :=
  NativeFx.Source.revertInsufficient (getAddr256 map key) want

@[pf_inline] def revertInsufficientPair256 (map : MapPair256) (owner spender : Addr20)
    (want : UInt256) : UInt64 :=
  NativeFx.Source.revertInsufficient (getPair256 map owner spender) want

end ProofForge.Evm.HashedMap.Source
