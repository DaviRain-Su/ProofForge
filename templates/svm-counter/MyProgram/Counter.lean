import ProofForge.Attr
import ProofForge.Svm.Sdk

/-!
最小 SVM 程序模板：只导入 Attr + Svm.Sdk。
不要 `import ProofForge`（会拖进 Emit/Assemble/Registry）。
-/

namespace MyProgram.Counter

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

@[pf_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

end MyProgram.Counter
