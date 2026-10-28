import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContextBaseNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContextBaseInput

namespace OAI.Algorithms

/-! A concrete branch context for the literal residual program, including
actual node evaluation, reconstruction, complete high assignment counting,
and the fixed produced runtime envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

theorem branch_context (occurrence qi : ℕ) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hsource : ∀clause∈source,clause.length ≤ k)
    (hw : ∀i,(initial.stacks i).length ≤ W) (hb : NodeNative.Blank initial)
    (he : ∀i,i∈entryBlankPorts → initial.stacks i=[])
    (hr : q.Ready initial) (hn : 2 ≤ ProducedQueryResources.ambient q)
    (hsmall : ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q))
    (hindex : q.index=Encoding.encodeNat (markIndex q)) (h728 : initial.stacks 728=[])
    (original : Factor.Data)
    (hf : ∀i,Query.Protected i → i≠323 → initial.stacks i=original.stacks i)
    (hc : ∀i,i∈PreparedBranchContext.blankPorts → initial.stacks i=[]) :
    let spec := fixedSpec p hv source hs (nodeIndex p 0)
    ∃ B width, ∃ ctx : Marked.Wide.BranchContext Residual.command
      (Marked.Wide.maskCopied (Query.prepared p.out)) (Query.ProtectedWork original)
      (PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause) B width,
      ctx.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap p occurrence qi)
        (Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
          Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent) ∧
      ctx.stepWidth ≤ Query.Cost.ordinaryCap p occurrence qi ∧
      ctx.referenceBound ≤ Query.Cost.ordinaryCap p occurrence qi := by
  dsimp only
  let spec := fixedSpec p hv source hs (nodeIndex p 0)
  let U := Query.Cost.ordinaryCap p occurrence qi
  let K := Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
    Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent
  have hres := residual_spec p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
  let ctx := PreparedBranchContext.ofRankResidualSpec p Residual.command original hf hc hw
    (Query.Cost.residualCap U K) (PreparedRecovery.countWidth p)
    (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause hres
  refine ⟨_,_,ctx,le_rfl,?_,?_⟩
  · exact Query.Cost.prepared_countWidth_le p occurrence qi hw hn hsmall
  · exact Query.Cost.incoming_le_ordinary p occurrence qi

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
