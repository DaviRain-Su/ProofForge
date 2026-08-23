import Examples.Tree
import ProofForge

namespace Tests.TreeSpec

open Examples.Tree

#guard (init 0).root == 0
#guard (init 0).size == 0
#guard getRoot (init 0) == 0
#guard getSize (init 0) == 0
#guard getHead (init 0) == 0
#guard getAt (init 0) 0 == 0
#guard getAt (init 0) 9 == 0
#guard sentinel == 0
#guard emptyNode.left == 0
#guard emptyNode.color == 0

#guard
  match setHead (init 0) 7 with
  | .ok (st, ret) => st.nodes[0]!.value == 7 && ret == 7 && st.nodes[0]!.left == 0
  | .error _ => false

#guard
  match setAt (init 0) 1 9 with
  | .ok (st, ret) => st.nodes[1]!.value == 9 && ret == 9 && st.nodes[0]!.value == 0
  | .error _ => false

#guard
  match setAt (init 0) 9 1 with
  | .error .overflow => true
  | _ => false

#guard getRight (init 0) 0 == 0

#guard
  match setRight (init 0) 0 2 with
  | .ok (st, ret) => st.nodes[0]!.right == 2 && ret == 2 && st.nodes[0]!.value == 0
  | .error _ => false

#guard
  match setParent (init 0) 1 1 with
  | .ok (st, ret) => st.nodes[1]!.parent == 1 && ret == 1 && st.nodes[0]!.parent == 0
  | .error _ => false

#guard
  match bumpInsert (init 0) 3 7 with
  | .ok (st, ret) =>
      st.root == 1 && st.size == 1 && ret == 3 &&
        st.nodes[0]!.key == 3 && st.nodes[0]!.value == 7 &&
        st.nodes[0]!.color == 1 && st.nodes[0]!.parent == 0
  | .error _ => false

#guard
  match bumpInsert (init 0) 3 7 with
  | .ok (st, _) =>
    match bumpInsert st 2 9 with
    | .ok (st2, ret) =>
        st2.size == 2 && ret == 2 &&
          st2.nodes[1]!.key == 2 && st2.nodes[1]!.value == 9 &&
          st2.nodes[1]!.parent == 1 && st2.nodes[0]!.value == 7 &&
          st2.nodes[0]!.right == 2
    | .error _ => false
  | .error _ => false

#guard
  match bumpInsert { (init 0) with
      root := 1, size := 2
      nodes := (init 0).nodes.set 0 { left := 0, right := 2, parent := 0, color := 1, key := 3, value := 7 }
    } 4 1 with
  | .error .overflow => true
  | _ => false

#guard
  (ProofForge.Golden.extractedTree.fields.find? (· == "nodes_0_value")).isSome
#guard ProofForge.IR.dataLen ProofForge.Golden.extractedTree == 216

end Tests.TreeSpec
