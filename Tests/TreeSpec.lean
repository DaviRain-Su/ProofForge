import Examples.Tree
import ProofForge

namespace Tests.TreeSpec

open Examples.Tree
open Lean Elab Command

elab "#pf_guard_tree_allocator" : command => do
  let env ← getEnv
  let program ←
    match ProofForge.Extract.extractModule env `Examples.Tree none with
    | .ok program => pure program
    | .error reason => throwError reason
  let asm ←
    match ProofForge.Svm.Emit.emitCounterAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless ProofForge.IR.dataLen program == 232 do
    throwError s!"Tree source account layout changed: {ProofForge.IR.dataLen program} bytes"
  let some alloc := program.methods.find? (·.ixName == "allocNode")
    | throwError "missing allocNode"
  let some release := program.methods.find? (·.ixName == "releaseNode")
    | throwError "missing releaseNode"
  unless alloc.paramCount == 2 && release.paramCount == 1 do
    throwError "Tree allocator ABI changed"
  let labels := (asm.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.endsWith ":" then some line else none
  unless labels.length == labels.eraseDups.length do
    throwError "Tree allocator assembly contains duplicate labels"

#pf_guard_tree_allocator

#guard (init 0).root == 0
#guard (init 0).size == 0
#guard (init 0).bumpIndex == 1
#guard (init 0).freeHead == 1
#guard getRoot (init 0) == 0
#guard getSize (init 0) == 0
#guard getBumpIndex (init 0) == 1
#guard getFreeHead (init 0) == 1
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
  match allocNode (init 0) 10 100 with
  | .ok (st, address) =>
      address == 1 && st.size == 1 && st.bumpIndex == 2 && st.freeHead == 2 &&
        st.nodes[0]!.key == 10 && st.nodes[0]!.value == 100 && st.nodes[0]!.left == 0
  | .error _ => false

#guard
  match allocNode (init 0) 10 100 with
  | .ok (st, _) =>
    match releaseNode st 1 with
    | .ok (freed, address) =>
      match allocNode freed 20 200 with
      | .ok (reused, reusedAddress) =>
          address == 1 && reusedAddress == 1 && reused.size == 1 &&
            reused.bumpIndex == 2 && reused.freeHead == 2 &&
            reused.nodes[0]!.left == 0 && reused.nodes[0]!.key == 20 &&
            reused.nodes[0]!.value == 200
      | .error _ => false
    | .error _ => false
  | .error _ => false

#guard
  match allocNode (init 0) 10 100 with
  | .ok (s1, _) =>
    match allocNode s1 20 200 with
    | .ok (s2, _) =>
      match releaseNode s2 1 with
      | .ok (f1, _) =>
        match releaseNode f1 2 with
        | .ok (f2, _) =>
          match allocNode f2 30 300 with
          | .ok (r2, a2) =>
            match allocNode r2 40 400 with
            | .ok (r1, a1) =>
                a2 == 2 && a1 == 1 && r1.size == 2 && r1.bumpIndex == 3 &&
                  r1.freeHead == 3 && r1.nodes[1]!.left == 0 &&
                  r1.nodes[0]!.left == 0 && r1.nodes[1]!.value == 300 &&
                  r1.nodes[0]!.value == 400
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

#guard
  match
    let s0 := { (init 0) with size := 4, bumpIndex := 5, freeHead := 5 }
    allocNode s0 1 1 with
  | .error .overflow => true
  | _ => false

#guard
  match bumpInsert (init 0) 3 7 with
  | .ok (st, ret) =>
      st.root == 1 && st.size == 1 && ret == 3 &&
        st.bumpIndex == 2 && st.freeHead == 2 &&
        st.nodes[0]!.key == 3 && st.nodes[0]!.value == 7 &&
        st.nodes[0]!.color == 1 && st.nodes[0]!.parent == 0
  | .error _ => false

#guard
  match bumpInsert (init 0) 3 7 with
  | .ok (st, _) =>
    match bumpInsert st 2 9 with
    | .ok (st2, ret) =>
        st2.size == 2 && ret == 2 &&
          st2.bumpIndex == 3 && st2.freeHead == 3 &&
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
  match
    let s0 :=
      { (init 0) with
        root := 1, size := 2
        nodes :=
          ((init 0).nodes.set 0 { left := 0, right := 2, parent := 0, color := 1, key := 3, value := 7 }).set 1
            { left := 0, right := 0, parent := 1, color := 1, key := 2, value := 9 } }
    rotateLeft s0 0 with
  | .ok (st, y) =>
      y == 2 && st.nodes[0]!.right == 0 &&
        st.nodes[1]!.left == 1 && st.nodes[1]!.parent == 0
  | .error _ => false

#guard
  (ProofForge.Golden.extractedTree.fields.find? (· == "nodes_0_value")).isSome
#guard ProofForge.IR.dataLen ProofForge.Golden.extractedTree == 216

end Tests.TreeSpec
