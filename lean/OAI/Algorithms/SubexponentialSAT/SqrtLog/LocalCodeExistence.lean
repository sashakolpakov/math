import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeCounting
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

/-! Exact finite random-row counting, with no probabilistic hypothesis. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators
open SparseCode

section Evaluation

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def evaluationHom (v : C → F3) : CheckMatrix R C →+ (R → F3) where
  toFun Q := check Q v
  map_zero' := by ext r; simp [check]
  map_add' Q Q' := by ext r; simp [check, add_mul, Finset.sum_add_distrib]

omit [Fintype R] [DecidableEq R] in
theorem evaluationHom_surjective {v : C → F3} (hv : v ≠ 0) :
    Function.Surjective (evaluationHom (R := R) v) := by
  classical
  have hex : ∃ c, v c ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨c, hc⟩ := hex
  intro y
  refine ⟨fun r c' => if c' = c then y r / v c else 0, ?_⟩
  ext r
  simp [evaluationHom, check, ite_mul, hc]

omit [Fintype R] [DecidableEq R] [DecidableEq C] in
theorem evaluationHom_eq_zero_iff (v : C → F3) (Q : CheckMatrix R C) :
    evaluationHom v Q = 0 ↔ IsCodeword Q v := by
  exact Iff.intro (fun h r => congrFun h r) (fun h => funext h)

noncomputable def killedMatrices (v : C → F3) : Finset (CheckMatrix R C) :=
  Finset.univ.filter fun Q => evaluationHom v Q = 0

theorem killedMatrices_card {v : C → F3} (hv : v ≠ 0) :
    (killedMatrices (R := R) v).card * 3 ^ Fintype.card R =
      Fintype.card (CheckMatrix R C) := by
  classical
  have h := card_zero_fiber_mul (evaluationHom (R := R) v)
    (evaluationHom_surjective hv)
  simpa only [Fintype.card_subtype, Fintype.card_fun, ZMod.card,
    killedMatrices] using h

theorem exists_matrix_avoiding
    (s : Finset (C → F3)) (hzero : ∀ v ∈ s, v ≠ 0)
    (hsmall : s.card < 3 ^ Fintype.card R) :
    ∃ Q : CheckMatrix R C, ∀ v ∈ s, ¬ IsCodeword Q v := by
  classical
  obtain ⟨Q, hQ⟩ := exists_avoiding_of_budget s
    (killedMatrices (R := R)) (3 ^ Fintype.card R)
    (fun v hv => (killedMatrices_card (hzero v hv)).le) hsmall
  refine ⟨Q, fun v hv hcode => hQ v hv ?_⟩
  simp only [killedMatrices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (evaluationHom_eq_zero_iff v Q).mpr hcode

end Evaluation

/-- The combinatorial existence criterion for a finite local code. Its
cardinality hypothesis will be discharged by the low-weight word estimate. -/
theorem exists_distance_of_card (D t d : ℕ)
    (hsmall : (Finset.univ.filter fun v : Fin D → F3 =>
      v ≠ 0 ∧ weight v < d).card < 3 ^ t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D), HasDistance Q d := by
  classical
  obtain ⟨Q, hQ⟩ := exists_matrix_avoiding (R := Fin t)
    (Finset.univ.filter fun v : Fin D → F3 => v ≠ 0 ∧ weight v < d)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2.1)
    (by simpa using hsmall)
  refine ⟨Q, fun v hv hv0 => ?_⟩
  by_contra h
  exact hQ v (by simp [hv0, Nat.lt_of_not_ge h]) hv

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
