import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryNative

namespace OAI.Algorithms

/-! Small range and canonical-encoding consequences of the actual query and
head producer. These introduce no extra coverage or parser promises. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

theorem query_scopes_le_factors (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    q.scopeRows.length ≤ (LeafProgram.Query.packingProblem q k hg).factors := by
  exact PackingIncidenceInput.Semantics.counter_mono q.scopeRows q.forward 0 q.scopeRows.length

theorem query_rows_le_factors (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    q.rows.length ≤ (LeafProgram.Query.packingProblem q k hg).factors := by
  have hs := query_scopes_le_factors q k hg
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length] at hs
  omega

theorem query_marked_lt_factors (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) (hm : q.mark.isSome=true) :
    q.rows.length < (LeafProgram.Query.packingProblem q k hg).factors := by
  have hs := query_scopes_le_factors q k hg
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length,hm] at hs
  simp only [Bool.toNat_true] at hs
  omega

theorem producedHead_context_canonical {base : LeafHeadSetupProgram.Data}
    {n N D B z : ℕ} {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {table : HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHead base n N D rows low Rel B z table) :
    table.context=ProgramEncoding.encodeRecords
      ((LeafStatisticsProgram.Arity.decoded table.context).map SubexponentialSAT.Encoding.encodeNat) := by
  obtain ⟨mr,ys,hr,hy,ht⟩ := hp
  rw [ht]
  simp only [LeafHeadSetupProgram.selectedContext,records_encode_nat,
    LeafStatisticsProgram.Arity.decoded_encode]

theorem producedHead_context_bound {base : LeafHeadSetupProgram.Data}
    {n N D B z : ℕ} {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {table : HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHead base n N D rows low Rel B z table)
    (f : ℕ) (hf : f∈LeafStatisticsProgram.Arity.decoded table.context) : f < N := by
  obtain ⟨mr,ys,hr,hy,ht⟩ := hp
  rw [ht] at hf
  simp only [LeafHeadSetupProgram.selectedContext,records_encode_nat,
    LeafStatisticsProgram.Arity.decoded_encode] at hf
  exact List.mem_range.mp (List.mem_filter.mp hf).1

theorem producedHeads_context_canonical {base : LeafHeadSetupProgram.Data}
    {n N D B z : ℕ} {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (i : Fin tables.length) :
    (tables.get i).context=ProgramEncoding.encodeRecords
      ((LeafStatisticsProgram.Arity.decoded (tables.get i).context).map SubexponentialSAT.Encoding.encodeNat) :=
  producedHead_context_canonical (producedHeads_get hp i)

theorem producedHeads_context_bound {base : LeafHeadSetupProgram.Data}
    {n N D B z : ℕ} {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (i : Fin tables.length) (f : ℕ)
    (hf : f∈LeafStatisticsProgram.Arity.decoded (tables.get i).context) : f < N :=
  producedHead_context_bound (producedHeads_get hp i) f hf

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end OAI.Algorithms
