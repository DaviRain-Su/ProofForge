import ProofForge.Extract.IR

namespace Tests.CFGSpec

open ProofForge

private def branchProgram : Array ProofForge.Extract.IR.Op := #[
  .ite .eq (.arg 0) (.lit 0)
    #[.storeField "value" (.lit 1)]
    #[.storeField "value" (.lit 2)],
  .returnState (.arg 0)
]

#guard match ProofForge.Extract.IR.toCFG branchProgram with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some { terminator := .branch _ _ _ thenEdge elseEdge, .. } =>
          match graph.block? thenEdge.target, graph.block? elseEdge.target with
          | some { terminator := .jump thenJoin, .. },
              some { terminator := .jump elseJoin, .. } => thenJoin.target == elseJoin.target
          | _, _ => false
      | _ => false

private def emptyArms : Array ProofForge.Extract.IR.Op := #[
  .ite .eq (.arg 0) (.lit 0) #[] #[],
  .returnU64 (.lit 7)
]

-- Identical branch blocks are interned after the explicit continuation has been formed.
#guard match ProofForge.Extract.IR.toCFG emptyArms with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some { terminator := .branch _ _ _ thenEdge elseEdge, .. } =>
          thenEdge.target == elseEdge.target
      | _ => false

private def loopProgram : Array ProofForge.Extract.IR.Op := #[
  .forBody 3 #[.storeField "value" .loopIx],
  .returnState (.arg 0)
]

#guard match ProofForge.Extract.IR.toCFG loopProgram with
  | .error _ => false
  | .ok graph =>
      graph.blocks.all (fun block => block.instructions.all fun
        | .forBody .. | .ite .. => false
        | _ => true) &&
      graph.blocks.any fun block => block.instructions.any fun
        | .storeField "value" (.local _) => true
        | _ => false

private def nestedLoops : Array ProofForge.Extract.IR.Op := #[
  .forBody 2 #[
    .forBody 2 #[.storeField "inner" .loopIx],
    .storeField "outer" .loopIx
  ],
  .returnState (.arg 0)
]

#guard match ProofForge.Extract.IR.toCFG nestedLoops with
  | .error _ => false
  | .ok graph =>
      let loopLocals := graph.blocks.flatMap fun block =>
        block.instructions.filterMap fun
          | .storeField "inner" (.local id) | .storeField "outer" (.local id) => some id
          | _ => none
      loopLocals.toList.eraseDups.length == 2

private def duplicateExpression : Array ProofForge.Extract.IR.Op := #[
  .letLocal 0 (.addU64 (.arg 0) (.lit 1)),
  .letLocal 1 (.addU64 (.arg 0) (.lit 1)),
  .returnU64 (.local 1)
]

#guard match ProofForge.Extract.IR.toCFG duplicateExpression with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some block =>
          block.instructions.size == 1 &&
            match block.terminator with
            | .exit (.returnU64 (.local 0)) => true
            | _ => false
      | none => false

private def tupleReturn : Array ProofForge.Extract.IR.Op := #[
  .returnU64 (.arg 0),
  .returnU64 (.arg 1)
]

-- A CFG exit retains the complete ABI tuple instead of silently dropping values after the first.
#guard match ProofForge.Extract.IR.toCFG tupleReturn with
  | .ok graph =>
      (graph.block? graph.entry).any fun block =>
        block.terminator == .exit (.returnU64s #[.arg 0, .arg 1])
  | .error _ => false

private def checkedProgram : Array ProofForge.Extract.IR.Op := #[
  .checkedAddU64 (.arg 0) (.lit 1),
  .okState (.arg 0),
  .errorOverflow
]

#guard match ProofForge.Extract.IR.toCFG checkedProgram with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some { terminator := .checked (.addU64 _ _) success overflow, .. } =>
          match graph.block? success.target, graph.block? overflow.target with
          | some { terminator := .exit (.okState _), .. },
              some { terminator := .exit .errorOverflow, .. } => true
          | _, _ => false
      | _ => false

private def evmEffectProgram : Array ProofForge.Extract.IR.Op := #[
  .letLocal 0 (.arg 0),
  .letLocal 1 (.arg 0),
  .ext (.evm (.deposit (.local 1))),
  .returnU64 (.local 1)
]

-- Target payload operands participate in substitution without making the CSE pass target-specific.
#guard match ProofForge.Extract.IR.toCFG evmEffectProgram with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some block =>
          block.instructions.size == 2 &&
            (match block.instructions[0]?, block.instructions[1]?, block.terminator with
            | some (ProofForge.Core.Ops.Op.letLocal 0 _),
                some (ProofForge.Core.Ops.Op.ext
                  (ProofForge.Extract.IR.OpExt.evm
                    (ProofForge.Evm.Ops.OpExt.deposit (.local 0)))),
                .exit (.returnU64 (.local 0)) => true
            | _, _, _ => false)
      | _ => false

private def crossBlockUse : Array ProofForge.Extract.IR.Op := #[
  .letLocal 0 (.arg 0),
  .letLocal 1 (.arg 0),
  .ite .eq (.arg 0) (.lit 0) #[.returnU64 (.local 1)] #[.returnU64 (.local 1)]
]

-- A local used by successor blocks is not removed without a dominance-aware global rewrite.
#guard match ProofForge.Extract.IR.toCFG crossBlockUse with
  | .error _ => false
  | .ok graph =>
      (graph.block? graph.entry).any (·.instructions.size == 2)

private def mutableRepresentative : Array ProofForge.Extract.IR.Op := #[
  .letLocal 0 (.arg 0),
  .letLocal 1 (.arg 0),
  .setLocal 0 (.lit 9),
  .returnU64 (.local 1)
]

-- CSE must not alias through a local that is assigned later in the block.
#guard match ProofForge.Extract.IR.toCFG mutableRepresentative with
  | .error _ => false
  | .ok graph =>
      match graph.block? graph.entry with
      | some block => block.instructions.size == 3 &&
          block.terminator == .exit (.returnU64 (.local 1))
      | none => false

private def danglingGraph : ProofForge.Extract.IR.CFG := {
  entry := 0
  blocks := #[{
    id := 0
    terminator := .jump { target := 1 }
  }]
}

#guard match danglingGraph.validate with
  | .error _ => true
  | .ok _ => false

end Tests.CFGSpec
