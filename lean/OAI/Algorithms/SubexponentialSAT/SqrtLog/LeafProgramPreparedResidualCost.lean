import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryWitness
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostTail

namespace OAI.Algorithms

/-! The actual branch trace budget is absorbed by the produced query cap. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

theorem residual_budget_le (occurrence qi K : ℕ)
    (hw : ∀i,(initial.stacks i).length ≤ W)
    (hn : 2 ≤ ProducedQueryResources.ambient q)
    (hsmall : ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q))
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (words : List (List Bool))
    (hshape : words.map List.length=List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (h331 : a.stacks 331=[]) (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[]) :
    Residual.Native.residualBound (Query.Width.incomingWidth p)
      (Residual.Native.highBound a (HighIncidenceProgram.Branches.trueCount q.forward.reverse))
      (Residual.Native.sampleBudget a (nodeFamily p) (fun _=>K)
        ((produce (q.input k)).J*((numeric q k p.lengths).val 34*baseWidth 3 ((numeric q k p.lengths).val 33)))
        (Query.packingProblem q k hg).Q) (PreparedRecovery.nativeCost p) ≤
      Query.Cost.residualCap (Query.Cost.ordinaryCap p occurrence qi) K := by
  have hi := Query.Cost.incoming_le_ordinary p occurrence qi
  have hwidth := residual_input_width p hw a ha words hshape hc h331 h323 h324
  have hh := counter_width_incoming p
  apply Query.Cost.residual_measured_le a (Query.Width.incomingWidth p)
    (HighIncidenceProgram.Branches.trueCount q.forward.reverse) (nodeFamily p) (fun _=>K)
    _ _ _ _ K hi
  · exact (hwidth 338 (by decide)).trans hi
  · omega
  · exact (nodes_le_incoming p hw).trans hi
  · rw [numeric_d q k p.lengths hg,numeric_t q k p.lengths hg]
    exact Query.Cost.produced_maxJet_le p occurrence qi hn hsmall
  · exact fun i _=>(node_word_le_incoming p hw i).trans hi
  · exact fun i _=>le_rfl
  · exact (hwidth 190 (by decide)).trans hi
  · exact (hwidth 191 (by decide)).trans hi
  · exact (hwidth 256 (by decide)).trans hi
  · exact Query.Cost.prepared_recovery_le p occurrence qi hw hn hsmall

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
