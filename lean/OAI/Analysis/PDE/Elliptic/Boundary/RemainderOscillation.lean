import OAI.Analysis.PDE.Elliptic.Boundary.PullbackOscillation
import OAI.Analysis.PDE.Elliptic.Boundary.BackgroundRemainder

/-! Interior scaled Hessian oscillation for the chart remainder after the
prescribed smooth background is subtracted. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem chart_remainder_scaled_oscillation {u B : E → ℝ} {G : E → E} {S : Set E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (hG : ContDiff ℝ 3 G)
    (hS : Convex ℝ S) (hV : 0 ≤ V)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ V)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S)
    {h β C K : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : 0 ≤ K) (hd : ‖z - z'‖ ≤ h)
    (hphys : ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤
      C * (‖z - z'‖ / h) ^ β)
    (hback : ‖fderiv ℝ (gradient (fun y => B (G y))) z -
      fderiv ℝ (gradient (fun y => B (G y))) z'‖ ≤ K * ‖z - z'‖) :
    ‖fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z'‖ ≤
      (V ^ 2 * C + 3 * V ^ 3 + V ^ 2 + K) * (‖z - z'‖ / h) ^ β := by
  have hpu : ContDiff ℝ 2 (fun y => u (G y)) := hu.comp (hG.of_le (by norm_num))
  have hpB : ContDiff ℝ 2 (fun y => B (G y)) := hB.comp (hG.of_le (by norm_num))
  have hbase := chart_hessian_scaled_oscillation hu hG hS hV hu1 hu2 hG1 hG2 hG3
    hz hz' hh hh1 hβ hβ1 hd hphys
  have hdp : ‖z - z'‖ ≤ (‖z - z'‖ / h) ^ β := by
    exact (le_div_self (norm_nonneg _) hh hh1).trans
      (Real.self_le_rpow_of_le_one (by positivity) ((div_le_one hh).2 hd) hβ1)
  have hback' := hback.trans (mul_le_mul_of_nonneg_left hdp hK)
  rw [hessianOperator_sub hpu hpB, hessianOperator_sub hpu hpB]
  have hid :
      (fderiv ℝ (gradient (fun y => u (G y))) z - fderiv ℝ (gradient (fun y => B (G y))) z) -
      (fderiv ℝ (gradient (fun y => u (G y))) z' - fderiv ℝ (gradient (fun y => B (G y))) z') =
      (fderiv ℝ (gradient (fun y => u (G y))) z - fderiv ℝ (gradient (fun y => u (G y))) z') -
      (fderiv ℝ (gradient (fun y => B (G y))) z - fderiv ℝ (gradient (fun y => B (G y))) z') := by abel
  rw [hid]
  exact (norm_sub_le _ _).trans ((add_le_add hbase hback').trans_eq (by ring))

end OAI.Analysis.PDE.Elliptic
