import OAI.Analysis.PDE.Elliptic.Boundary.PullbackBounds
import OAI.Analysis.PDE.Elliptic.TraceDual

/-! Quantitative recovery of the missing normal-normal Hessian entry from
the two supporting inequalities of a uniformly elliptic concave operator. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem traceRight_add_left (D R A : E →L[ℝ] E) :
    traceRight (D + R) A = traceRight D A + traceRight R A := by
  simp [traceRight, ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add]

omit [FiniteDimensional ℝ E] in
theorem traceRight_smul_left (t : ℝ) (D A : E →L[ℝ] E) :
    traceRight (t • D) A = t * traceRight D A := by
  simp [traceRight, ContinuousLinearMap.toLinearMap_smul]

omit [FiniteDimensional ℝ E] in
theorem traceRight_neg_left (D A : E →L[ℝ] E) : traceRight (-D) A = -traceRight D A := by
  simp [traceRight, ContinuousLinearMap.comp_neg, ContinuousLinearMap.toLinearMap_neg]

theorem traceRight_rankOne_left (A : E →L[ℝ] E) (v : E) :
    traceRight (rankOne ℝ v v) A = inner ℝ v (A v) := by
  rw [← traceRight_rankOne A v v]
  exact LinearMap.trace_mul_comm ℝ A.toLinearMap (rankOne ℝ v v).toLinearMap

theorem abs_traceRight_bound (D A : E →L[ℝ] E) :
    |traceRight D A| ≤ Module.finrank ℝ E * ‖A‖ * ‖D‖ := by
  have hm := mul_le_mul_of_nonneg_left (A.opNorm_comp_le D) (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E))
  exact (abs_trace_le_finrank_norm (A.comp D)).trans
    (by simpa only [mul_assoc] using hm)

theorem normal_entry_recovery (A B R : E →L[ℝ] E) (v : E) {t delta lam N : ℝ}
    (_ : 0 ≤ lam) (_ : 0 ≤ N)
    (hA : lam ≤ inner ℝ v (A v)) (hB : lam ≤ inner ℝ v (B v))
    (hAn : ‖A‖ ≤ N) (hBn : ‖B‖ ≤ N)
    (hupper : delta ≤ traceRight (t • rankOne ℝ v v + R) A)
    (hlower : -delta ≤ traceRight (-(t • rankOne ℝ v v + R)) B) :
    lam * |t| ≤ |delta| + Module.finrank ℝ E * N * ‖R‖ := by
  have hRA : |traceRight R A| ≤ Module.finrank ℝ E * N * ‖R‖ :=
    (abs_traceRight_bound R A).trans (by gcongr)
  have hRB : |traceRight R B| ≤ Module.finrank ℝ E * N * ‖R‖ :=
    (abs_traceRight_bound R B).trans (by gcongr)
  rw [traceRight_add_left, traceRight_smul_left, traceRight_rankOne_left] at hupper
  rw [traceRight_neg_left, traceRight_add_left, traceRight_smul_left, traceRight_rankOne_left] at hlower
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have hmul := mul_le_mul_of_nonneg_left hB ht
    linarith [le_abs_self delta, neg_abs_le (traceRight R B)]
  · rw [abs_of_nonpos ht]
    have hmul := mul_le_mul_of_nonpos_left hA ht
    linarith [neg_abs_le delta, le_abs_self (traceRight R A)]

end OAI.Analysis.PDE.Elliptic
