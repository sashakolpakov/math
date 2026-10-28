import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendMajorants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramFrontendInputBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafScopeInputBounds
open LeafParametersProgram.FrontendBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem parameter_counts_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    CountsBound (q.input k) (parameterSize (capacity q k)) := by
  have h := query_bounds q k hv
  have h0 := h.ambient
  have h1 := h.free
  have h2 := h.clauseCount
  have h3 := h.occurrence
  have h4 := h.arity
  have h5 := h.factors
  have h6 := h.widthParameter
  have h7 := h.incidences
  have hm := hv.2.2.2.2.2.1
  intro i
  fin_cases i
  · change BinaryArithmetic.toNat q.ambient ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).free ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change BinaryArithmetic.toNat q.modulus ≤ parameterSize (capacity q k)
    rw [hm]
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).occurrence ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change completedArity q.scopeRows q.forward ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change q.scopeRows.length+(totals q.scopeRows q.forward).uncovered ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change k ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).incidences ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega

theorem parameter_lengths_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    ∀ i, q.inputLengths k i ≤ parameterSize (capacity q k) := by
  intro i
  have h := numericCost_bound q k hv
  change q.numericCost k ≤ _
  unfold parameterSize
  omega

theorem hashCountBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.hashCountBudget ≤ 10*capacity q k+9 := by
  have hs := SubexpSunflowerProgram.CountRecords.steps_le_encoded
    (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
  have hr := (query_bounds q k hv).rowBits
  change (Encoding.encodeList id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))).length ≤
    capacity q k at hr
  unfold Query.hashCountBudget SubexpScopeCountSetup.countBudget
  dsimp only [SubexpSunflowerProgram.CountRecords.steps] at hs
  omega

theorem inputBudget_majorant (C d : ℕ)
    (hp : ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ), CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l)+
        5000*(2*(Execute.guardedModel x l).val 29+1)^2*
          ((Execute.guardedModel x l).len 3+(Execute.guardedModel x l).len 21+
            (Execute.guardedModel x l).len 29+11)^2 ≤ C*(S+1)^d)
    (q : Query) (k : ℕ) (hv : q.Valid) :
    q.inputBudget k ≤ finalMajorant C d (capacity q k) := by
  have hc := coreInputBudget_bound q k hv
  have hh := hashCountBudget_bound q k hv
  have hn := (query_bounds q k hv).ambient
  have hb := hp (q.input k) (q.inputLengths k) (parameterSize (capacity q k))
    (parameter_counts_bound q k hv) (parameter_lengths_bound q k hv)
  change Execute.runtimeBound (q.input k) (q.inputLengths k)+
    Exports.prepareBudget (Execute.guardedModel (q.input k) (q.inputLengths k))+
    offsetModelBudget (Execute.guardedModel (q.input k) (q.inputLengths k)) ≤
      C*(parameterSize (capacity q k)+1)^d at hb
  unfold Query.inputBudget postUniformBudget postPrefixBudget finalMajorant
  omega

/-- One fixed polynomial bounds the complete frontend from its physical input
capacity, uniformly over queries and fixed-width choices. -/
theorem inputBudget_polynomial :
    ∃ C d : ℕ, ∀ (q : Query) (k : ℕ), q.Valid →
      q.inputBudget k ≤ C*(capacity q k+1)^d := by
  obtain ⟨C,d,hp⟩ := uniform_offset_polynomial
  obtain ⟨A,e,ha⟩ := finalMajorant_poly C d
  exact ⟨A,e,fun q k hv => (inputBudget_majorant C d hp q k hv).trans (ha (capacity q k))⟩

/-- Every actual native frontend run satisfies the same ordinary-polynomial
bound; no intermediate state, computed parameter, or free statistics input is
assumed in this theorem. -/
theorem frontend_time_polynomial :
    ∃ C d : ℕ, ∀ (q : Query) (k : ℕ) (a b : Data) (n : ℕ),
      q.Valid → q.Ready a → q.OutputEmpty a → Eval (frontend k) n a b →
      n ≤ C*(capacity q k+1)^d := by
  obtain ⟨C,d,h⟩ := inputBudget_polynomial
  exact ⟨C,d,fun q k a b n hv ha ho he => (frontend_time_le q k hv ha ho he).trans (h q k hv)⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
