import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheContext
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheRow

namespace OAI.Algorithms

/-! The outer Lagrange loop invariant, instantiated by the actual prepared
cache store. These are state identities and input-layout proofs; the row
and loop commands remain the independently defined physical programs. -/

namespace SubexponentialSAT.SubexpLagrangeCacheInvariant

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open SubexpLagrangeCacheState
open SubexpLagrangeCachePreparation

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

omit [Fact p.Prime] in
theorem view_empty (x : Inputs) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) (k : Fin 256)
    (hk : k ∉ SubexpLagrangeCacheContext.support) (h248 : k ≠ 248) :
    SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one i cache todo k = [] := by
  have h217 : k ≠ 217 := by
    intro he
    subst k
    exact hk (by decide)
  have h250 : k ≠ 250 := by
    intro he
    subst k
    exact hk (by decide)
  have h246 : k ≠ 246 := by
    intro he
    subst k
    exact hk (by decide)
  rw [SubexpLagrangeCacheOuterState.view_frame p μ M (preparedStore x) zero one i
    cache todo k h217 h248 h250 h246]
  exact SubexpLagrangeCacheContext.prepared_empty x k hk

omit [Fact p.Prime] in
/-- Every row begins with the required physical operands and clean scratch
cells. The polynomial dimension is the prime supplied to preparation. -/
theorem environment (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne)
    (i : ℕ) (cache : List (List (List Bool))) (todo : List Bool) :
    SubexpLagrangeCacheRow.Environment p μ M p t zero one minusOne
      x.width x.exponent x.precision
      (SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one i cache todo) i := by
  obtain ⟨h207, h211, h213, h217, h224, h225, h243, h246, h250⟩ :=
    SubexpLagrangeCacheContext.prepared_high p μ M x t zero one minusOne H
  have Hwork := SubexpLagrangeCacheContext.prepared_workspace p μ M x t zero one minusOne H
  refine {
    toEnvironment := {
      width_eq := H.width
      workspace := SubexpLagrangeCacheOuterState.view_workspace p μ M (preparedStore x)
        t zero one x.width Hwork i cache todo
      zero_eq := H.zero
      one_eq := ?_
      minus_eq := ?_
      theta_eq := ?_
      index_eq := ?_
      label_eq := ?_
      zero_array := ?_
      dimension := ?_
      empty := ?_ }
    exponent_eq := ?_
    counter_eq := ?_
    fresh := ?_ }
  · simpa [SubexpLagrangeCacheOuterState.view] using h207
  · simpa [SubexpLagrangeCacheOuterState.view] using h211
  · simpa [SubexpLagrangeCacheOuterState.view] using h213
  · simp [SubexpLagrangeCacheOuterState.view]
  · simp [SubexpLagrangeCacheOuterState.view]
  · simpa [SubexpLagrangeCacheOuterState.view, encode] using
      SubexpLagrangeCacheContext.prepared_zeroArray p μ M x t zero one minusOne H
  · simpa [SubexpLagrangeCacheOuterState.view] using h243
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact view_empty p μ M x zero one i cache todo _ (by decide) (by decide)
  · simpa [SubexpLagrangeCacheOuterState.view] using h225
  · simpa [SubexpLagrangeCacheOuterState.view] using h224
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      exact view_empty p μ M x zero one i cache todo _ (by decide) (by decide)

omit [Fact p.Prime] in
/-- No logical relabelling of the initial machine store is needed: the
prepared bytes themselves are the zero-row outer invariant. -/
theorem initial_view (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne) :
    SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one 0 []
      (List.replicate p true) = preparedStore x := by
  obtain ⟨h207, h211, h213, h217, h224, h225, h243, h246, h250⟩ :=
    SubexpLagrangeCacheContext.prepared_high p μ M x t zero one minusOne H
  have h248 : preparedStore x 248 = [] :=
    SubexpLagrangeCacheContext.prepared_empty x 248 (by decide)
  funext k
  by_cases hk217 : k = 217
  · subst k
    simp [SubexpLagrangeCacheOuterState.view, label, h217]
  · by_cases hk248 : k = 248
    · subst k
      simp [SubexpLagrangeCacheOuterState.view, h248]
    · by_cases hk250 : k = 250
      · subst k
        simp [SubexpLagrangeCacheOuterState.view, h250]
      · by_cases hk246 : k = 246
        · subst k
          simp [SubexpLagrangeCacheOuterState.view, h246]
        · simp [SubexpLagrangeCacheOuterState.view, hk217, hk248, hk250, hk246]

omit [Fact p.Prime] in
theorem view_cache (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) :
    SubexpLagrangeCacheOuterState.view p μ M base zero one i cache todo 250 =
      Subexp.FactorPacketCoordinates.cacheBytes cache := by
  simp [SubexpLagrangeCacheOuterState.view]

omit [Fact p.Prime] in
/-- The row program's actual output is exactly the successor outer state,
including the framed row order and the unmodified remaining counter. -/
theorem output_view (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) (row : List (List Bool)) :
    SubexpLagrangeCacheRow.output p μ M
      (SubexpLagrangeCacheOuterState.view p μ M base zero one i cache todo)
      zero one i row cache =
    SubexpLagrangeCacheOuterState.view p μ M base zero one (i + 1) (row :: cache) todo := by
  simpa only [SubexpLagrangeCacheRow.output, List.replicate_succ] using
    SubexpLagrangeCacheOuterState.view_next p μ M base zero one i cache todo row

end SubexponentialSAT.SubexpLagrangeCacheInvariant

end OAI.Algorithms
