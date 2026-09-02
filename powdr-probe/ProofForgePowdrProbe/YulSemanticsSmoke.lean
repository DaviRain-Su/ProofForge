import YulSemantics.Ast
import YulSemantics.Dialect.EVMOp

/-!
Smoke import for powdr-labs/yul-semantics (Feature B intermediate semantics).
-/

namespace ProofForgePowdrProbe

abbrev smokeYulIdent := YulSemantics.Ident

/-- EVM dialect builtin op enum is linked. -/
abbrev smokeYulEvmOp := YulSemantics.EVM.Op

end ProofForgePowdrProbe
