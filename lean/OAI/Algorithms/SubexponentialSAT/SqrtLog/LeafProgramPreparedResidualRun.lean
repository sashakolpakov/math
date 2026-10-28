import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualRunCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodePost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing MomentsAssembly
open Residual.Native LeafNodeSamplesProgram
noncomputable section
attribute [local irreducible] Execute.guardedModel

theorem residual_run : ∀
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
    ∀ (a : Factor.Data),
    Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a →
    ∀ (words : List (List Bool)),
    words.map List.length=List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1 →
    a.stacks 330=Encoding.encodeList id words →
    a.stacks 331=[] → a.stacks 323=[] → a.stacks 324=[] →
    ∃ time out,
    time ≤ residualBound (Query.Width.incomingWidth p)
      (highBound a (HighIncidenceProgram.Branches.trueCount q.forward.reverse))
      (sampleBudget a (nodeFamily p) (fun _=>Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
          Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
      ((produce (q.input k)).J*((numeric q k p.lengths).val 34*baseWidth 3 ((numeric q k p.lengths).val 33)))
      (Query.packingProblem q k hg).Q) (PreparedRecovery.nativeCost p) ∧
    Eval Residual.command time a out ∧
    BinaryArithmetic.toNat (out.stacks 323)=
      PreparedRecovery.fixedHighCount p hv source hs (nodeIndex p 0) words.flatten ∧
    (out.stacks 323).length ≤ PreparedRecovery.countWidth p ∧ out.stacks 324=[] ∧
    out.stacks=Function.update a.stacks 323 (out.stacks 323) ∧ RegFrame a.regs out.regs :=
  residual_run_core PreparedNodePost.collector_nodePost

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
