import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativePreparedInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedQueryContext

namespace OAI.Algorithms

/-! The actual residual program and the exact decoded-row identity close the
outer count context. There is no supplied evaluator or count equation. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram LeafParametersProgram
noncomputable section

 theorem marked_prepared_context {n B k qi : ℕ} (F : OuterQuery.Formula n)
    (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width : ℕ) (hm : 0 < (formulaRecords F).length) (rows : HashSelectProgram.Records)
    (mark : Option (Fin (formulaRecords F).length))
    (hk : ∀C∈F,C.length ≤ k)
    (base : Query.Data)
    (input : MarkedInputFacts (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) mark) base)
    (facts : RuntimeFacts (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) mark)
      k B qi (markedCoefficient k) (markedExponent k))
    (hv : (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) mark).Valid)
    (hn : 2 ≤ ProducedQueryResources.ambient
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) mark))
    {V L : ℕ}
    (p : Query.Preparation (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) mark)
      k (Query.markedInput (Query.Carried.reference base)) facts.guard (Query.Carried.markedWidth base) V L) :
    Nonempty (PreparedCountContext p base (OuterQuery.Count.selectorCount F width rows mark) B qi) := by
  let raw := OuterQuery.Count.payloadRows F width hm rows
  let source := OuterQuery.querySource F a ha raw mark (Query.packingProblem _ k facts.guard).n rfl
  have hs := OuterQuery.querySource_bytes F a ha raw mark (Query.packingProblem _ k facts.guard).n rfl
  obtain ⟨budget,bits,ctx,hstep,hwidth,href⟩ := PreparedSource.marked_branch_context p B qi
    input.clean hv source hs (querySource_width F a ha raw mark _ rfl hk)
    (marked_input_width input) (marked_input_ready input) hn facts.small
    (query_index_canonical F a raw mark)
  have hc := OuterQuery.Count.fixedSpec_selectorCount F a ha width hm rows mark k p hv
    (PreparedSource.nodeIndex p 0)
  have result : Nonempty (PreparedCountContext p base
      (PreparedBranchCount.fullCount
        (NodeConcrete.sourceHashes (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)))
        (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)).marked
        (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)).markedClause) B qi) :=
    ⟨⟨budget,bits,ctx,hstep,hwidth,href⟩⟩
  exact hc ▸ result

 theorem accepted_prepared_context {n B k qi : ℕ} (F : OuterQuery.Formula n)
    (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width : ℕ) (hm : 0 < (formulaRecords F).length) (rows : HashSelectProgram.Records)
    (hk : ∀C∈F,C.length ≤ k)
    (base : Query.Data)
    (input : AcceptedInputFacts (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none) base)
    (facts : RuntimeFacts (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none)
      k B qi (acceptedCoefficient k) (acceptedExponent k))
    (hv : (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none).Valid)
    (hn : 2 ≤ ProducedQueryResources.ambient
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none))
    {V L : ℕ}
    (p : Query.Preparation (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none)
      k (Query.unmarkedInput (Query.Carried.reference base)) facts.guard (Query.Carried.acceptedWidth base) V L) :
    Nonempty (PreparedCountContext p base (OuterQuery.Count.selectorCount F width rows none) B qi) := by
  let raw := OuterQuery.Count.payloadRows F width hm rows
  let source := OuterQuery.querySource F a ha raw none (Query.packingProblem _ k facts.guard).n rfl
  have hs := OuterQuery.querySource_bytes F a ha raw none (Query.packingProblem _ k facts.guard).n rfl
  obtain ⟨budget,bits,ctx,hstep,hwidth,href⟩ := PreparedSource.unmarked_branch_context p B qi
    input.clean hv source hs (querySource_width F a ha raw none _ rfl hk)
    (accepted_input_width input) (accepted_input_ready input) hn facts.small
    (query_index_canonical F a raw none)
  have hc := OuterQuery.Count.fixedSpec_selectorCount F a ha width hm rows none k p hv
    (PreparedSource.nodeIndex p 0)
  have result : Nonempty (PreparedCountContext p base
      (PreparedBranchCount.fullCount
        (NodeConcrete.sourceHashes (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)))
        (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)).marked
        (PreparedSource.fixedSpec p hv source hs (PreparedSource.nodeIndex p 0)).markedClause) B qi) :=
    ⟨⟨budget,bits,ctx,hstep,hwidth,href⟩⟩
  exact hc ▸ result

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
