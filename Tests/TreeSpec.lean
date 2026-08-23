import Examples.Tree
import ProofForge

namespace Tests.TreeSpec

open Examples.Tree

#guard (init 0).root == 0
#guard (init 0).size == 0
#guard getRoot (init 0) == 0
#guard getSize (init 0) == 0
#guard getHead (init 0) == 0
#guard sentinel == 0
#guard emptyNode.left == 0
#guard emptyNode.color == 0

#guard
  match setHead (init 0) 7 with
  | .ok (st, ret) => st.nodes[0]!.value == 7 && ret == 7 && st.nodes[0]!.left == 0
  | .error _ => false

#guard
  (ProofForge.Golden.extractedTree.fields.find? (· == "nodes_0_value")).isSome
#guard ProofForge.IR.dataLen ProofForge.Golden.extractedTree == 216

end Tests.TreeSpec
