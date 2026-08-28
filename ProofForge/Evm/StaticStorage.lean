namespace ProofForge.Evm.StaticStorage

/-- Transitive effects for one ordered static-storage call. -/
structure EffectSummary where
  writesStorage : Bool := false
  deriving BEq, Repr, Inhabited

/--
Ordered static-storage effects whose destination is a compiler-static field name. Dynamic values
remain operands; target emission resolves the name against the extracted program schema instead
of accepting a source-visible slot number.
-/
inductive Call (V : Type) where
  | storeU64 (field : String) (value : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .storeU64 field value => .storeU64 field (mapValue value)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .storeU64 field value => return .storeU64 field (← mapValue value)

def Call.values : Call V → Array V
  | .storeU64 _ value => #[value]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .storeU64 .. => { writesStorage := true }

/-- Empty/dynamic field names fail the generic operation well-formedness gate. Unknown fields and
non-UInt64 widths fail later when the emitter resolves the call against the concrete program. -/
def Call.wellFormed (valueWellFormed : V → Bool) : Call V → Bool
  | .storeU64 field value => !field.isEmpty && valueWellFormed value

def Call.canonical (renderValue : V → String) : Call V → String
  | .storeU64 field value => s!"sstore.now.{field}({renderValue value})"

end ProofForge.Evm.StaticStorage
