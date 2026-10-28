import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeContext
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedEntry

namespace OAI.Algorithms

/-! Actual outer formula bytes and carried query states discharge the source,
ready, and width premises of the concrete residual context. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram
noncomputable section

 theorem transportFormula_width {n N k : ℕ} (F : OuterQuery.Formula n)
    (h : n=N) (hk : ∀C∈F,C.length ≤ k) :
    ∀C∈OuterQuery.transportFormula F h,C.length ≤ k := by
  subst N
  exact hk

 theorem querySource_width {n B k : ℕ} (F : OuterQuery.Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) (N : ℕ)
    (hN : N=ProducedQueryResources.ambient (OuterQuery.query F a rows mark))
    (hk : ∀C∈F,C.length ≤ k) :
    ∀C∈OuterQuery.querySource F a ha rows mark N hN,C.length ≤ k :=
  transportFormula_width F _ hk

 theorem query_index_canonical {n : ℕ} (F : OuterQuery.Formula n) (a : Data)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    (OuterQuery.query F a rows mark).index=
      Encoding.encodeNat (PreparedSource.markIndex (OuterQuery.query F a rows mark)) := by
  cases mark <;> rfl

 theorem marked_input_ready {q : LeafQueryFrontend.Query} {a : Query.Data}
    (h : MarkedInputFacts q a) : q.Ready (Query.markedInput (Query.Carried.reference a)) := by
  exact Query.marked_ready q _ (Query.Carried.reference_clean a h.clean)
    (Query.Carried.sources_reference q a h.sources) h.marked
    ((Query.Carried.reference_visible a 321 (by decide)).trans h.reference)

 theorem accepted_input_ready {q : LeafQueryFrontend.Query} {a : Query.Data}
    (h : AcceptedInputFacts q a) : q.Ready (Query.unmarkedInput (Query.Carried.reference a)) :=
  Query.accepted_ready q _ (Query.Carried.reference_clean a h.clean)
    (Query.Carried.sources_reference q a h.sources) h.unmarked h.index

 theorem marked_input_width {q : LeafQueryFrontend.Query} {a : Query.Data}
    (h : MarkedInputFacts q a) :
    ∀i,((Query.markedInput (Query.Carried.reference a)).stacks i).length ≤
      Query.Carried.markedWidth a :=
  Query.Carried.marked_source_width a h.clean h.zero h.high

 theorem accepted_input_width {q : LeafQueryFrontend.Query} {a : Query.Data}
    (h : AcceptedInputFacts q a) :
    ∀i,((Query.unmarkedInput (Query.Carried.reference a)).stacks i).length ≤
      Query.Carried.acceptedWidth a :=
  Query.Carried.accepted_source_width a h.clean h.zero h.high

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
