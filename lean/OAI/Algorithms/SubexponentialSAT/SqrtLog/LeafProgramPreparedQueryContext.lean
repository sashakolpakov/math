import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContext
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedEntry

namespace OAI.Algorithms

/-! The actual marked and unmarked query callers instantiate the complete
branch context without additional scratch-tape premises. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ}

def QueryContext {initial : Factor.Data}
    (p : Query.Preparation q k initial hg W V L) (occurrence qi : ℕ) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source) (original : Factor.Data) : Prop :=
  let spec := fixedSpec p hv source hs (nodeIndex p 0)
  ∃ B width, ∃ ctx : Marked.Wide.BranchContext Residual.command
    (Marked.Wide.maskCopied (Query.prepared p.out)) (Query.ProtectedWork original)
    (PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause) B width,
    ctx.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap p occurrence qi)
      (Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
        Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent) ∧
    ctx.stepWidth ≤ Query.Cost.ordinaryCap p occurrence qi ∧
    ctx.referenceBound ≤ Query.Cost.ordinaryCap p occurrence qi

theorem marked_branch_context
    (p : Query.Preparation q k (Query.markedInput (Query.Carried.reference a)) hg W V L)
    (occurrence qi : ℕ) (hc : Query.CleanWork a) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hsource : ∀clause∈source,clause.length ≤ k)
    (hw : ∀i,((Query.markedInput (Query.Carried.reference a)).stacks i).length ≤ W)
    (hr : q.Ready (Query.markedInput (Query.Carried.reference a)))
    (hn : 2 ≤ ProducedQueryResources.ambient q)
    (hsmall : ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q))
    (hindex : q.index=Encoding.encodeNat (markIndex q)) :
    QueryContext p occurrence qi hv source hs (Query.Carried.reference a) := by
  obtain ⟨hb,he,h728,hctrl⟩ := marked_initial a hc
  exact branch_context p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
    (Query.Carried.reference a) (PreparedBranchContext.marked_protected _) hctrl

theorem unmarked_branch_context
    (p : Query.Preparation q k (Query.unmarkedInput (Query.Carried.reference a)) hg W V L)
    (occurrence qi : ℕ) (hc : Query.CleanWork a) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hsource : ∀clause∈source,clause.length ≤ k)
    (hw : ∀i,((Query.unmarkedInput (Query.Carried.reference a)).stacks i).length ≤ W)
    (hr : q.Ready (Query.unmarkedInput (Query.Carried.reference a)))
    (hn : 2 ≤ ProducedQueryResources.ambient q)
    (hsmall : ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q))
    (hindex : q.index=Encoding.encodeNat (markIndex q)) :
    QueryContext p occurrence qi hv source hs (Query.Carried.reference a) := by
  obtain ⟨hb,he,h728,hctrl⟩ := unmarked_initial a hc
  exact branch_context p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
    (Query.Carried.reference a) (PreparedBranchContext.unmarked_protected _) hctrl

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
