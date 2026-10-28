import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualCost

namespace OAI.Algorithms

/-! The literal residual program satisfies the enclosing binary counter's
contract, with the produced uniform time and exact numeric branch count. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
open Residual.Native
noncomputable section
attribute [local irreducible] Execute.guardedModel

theorem residual_spec : ∀
    {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k initial hg W V L) (occurrence qi : ℕ)
    (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source),
    (∀clause∈source,clause.length ≤ k) →
    (∀i,(initial.stacks i).length ≤ W) → NodeNative.Blank initial →
    (∀i,i∈entryBlankPorts → initial.stacks i=[]) →
    q.Ready initial → 2 ≤ ProducedQueryResources.ambient q →
    ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q) →
    q.index=Encoding.encodeNat (markIndex q) → initial.stacks 728=[] →
    let spec := fixedSpec p hv source hs (nodeIndex p 0)
    LeafBranchProgram.ResidualSpec LeafBranchProgram.Wide.fixedPorts Residual.command
      (List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
      (Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)))
      (Query.Cost.residualCap (Query.Cost.ordinaryCap p occurrence qi)
        (Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
          Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent))
      (PreparedRecovery.countWidth p)
      (PreparedBranchCount.rankValue (NodeConcrete.planHigh (Query.packingProblem q k hg))
        (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause) := by
  intro q k initial hg W V L p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
  dsimp only
  intro words a hshape hready hc h331
  obtain ⟨time,out,ht,hev,hcount,hwidth,h324,hframe,hregs⟩ :=
    residual_run p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
      a hready.1 words hshape hc h331 hready.2.1 hready.2.2
  have htime := residual_budget_le p occurrence qi (Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
          Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
    hw hn hsmall a hready.1 words hshape hc h331 hready.2.1 hready.2.2
  have hf (i : Fin 768) (hi : i≠323) : out.stacks i=a.stacks i := by
    rw [hframe,Function.update_of_ne hi]
  refine ⟨time,out,ht.trans htime,hev,Residual.Branch.restored hready.1 hframe,?_,?_,?_,h324,hwidth,?_⟩
  · exact (hf 330 (by decide)).trans hc
  · exact (hf 331 (by decide)).trans h331
  · exact hf 332 (by decide)
  · exact hcount.trans (PreparedRecovery.fixedHighCount_eq_rank p hv source hs (nodeIndex p 0) words hshape)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
