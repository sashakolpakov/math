import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Error

/-! Oscillation of the actual pulled-back Hessian. The lower-order chart
error only uses two derivatives of u and three of the fixed chart. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem chart_hessian_oscillation_bound {u : E → ℝ} {G : E → E} {S : Set E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S) (hV : 0 ≤ V)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ V)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    ‖fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z'‖ ≤
      V ^ 2 * ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ +
        (3 * V ^ 3 + V ^ 2) * ‖z - z'‖ := by
  let J := fderiv ℝ G z
  let K := fderiv ℝ G z'
  let A := fderiv ℝ (gradient u) (G z)
  let B := fderiv ℝ (gradient u) (G z')
  have hid : fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z' =
      hessianCongruence J (A - B) +
        (hessianCongruence J B - hessianCongruence K B) +
        (chartCurvature u G z - chartCurvature u G z') := by
    rw [hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt,
      hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt]
    change (hessianCongruence J A + chartCurvature u G z) -
      (hessianCongruence K B + chartCurvature u G z') = _
    rw [hessianCongruence_sub]
    abel
  rw [hid]
  have hDG : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hJK : ‖J - K‖ ≤ V * ‖z - z'‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun y (_ : y ∈ S) => hDG.differentiable (by norm_num) y)
      (fun y hy => (second_fderiv_norm_le_iterated y).trans (hG2 y hy)) hS hz' hz
  have hvar : ‖hessianCongruence J B - hessianCongruence K B‖ ≤ 2 * V ^ 3 * ‖z - z'‖ := by
    apply (hessianCongruence_variation J K B).trans
    have h1 := mul_le_mul (mul_le_mul hJK (hu2 z' hz') (norm_nonneg _) (by positivity))
      (hG1 z hz) (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul (mul_le_mul (hG1 z' hz') (hu2 z' hz') (norm_nonneg _) hV)
      hJK (norm_nonneg _) (by positivity)
    dsimp [J, K, B] at *
    nlinarith
  have hcur := chartCurvature_lipschitz hu hG hS hV hu1 hu2 hG1 hG2 hG3 hz hz'
  have hmain : ‖hessianCongruence J (A - B)‖ ≤ V ^ 2 * ‖A - B‖ := by
    apply (hessianCongruence_norm J (A - B)).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [hG1 z hz, norm_nonneg J]) (norm_nonneg _)
  have hn := (norm_add_le (hessianCongruence J (A - B) +
    (hessianCongruence J B - hessianCongruence K B)) (chartCurvature u G z - chartCurvature u G z')).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  dsimp [A, B] at *
  nlinarith

theorem chart_hessian_scaled_oscillation {u : E → ℝ} {G : E → E} {S : Set E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S) (hV : 0 ≤ V)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ V)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S)
    {h β C : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (_ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hd : ‖z - z'‖ ≤ h)
    (hphys : ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤
      C * (‖z - z'‖ / h) ^ β) :
    ‖fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z'‖ ≤
      (V ^ 2 * C + 3 * V ^ 3 + V ^ 2) * (‖z - z'‖ / h) ^ β := by
  have hratio : 0 ≤ ‖z - z'‖ / h := div_nonneg (norm_nonneg _) hh.le
  have hratio1 : ‖z - z'‖ / h ≤ 1 := (div_le_one hh).2 hd
  have hdp : ‖z - z'‖ ≤ (‖z - z'‖ / h) ^ β := by
    calc
      ‖z - z'‖ ≤ ‖z - z'‖ / h := le_div_self (norm_nonneg _) hh hh1
      _ ≤ (‖z - z'‖ / h) ^ β := Real.self_le_rpow_of_le_one hratio hratio1 hβ1
  have hb := chart_hessian_oscillation_bound hu hG hS hV hu1 hu2 hG1 hG2 hG3 hz hz'
  have h1 := mul_le_mul_of_nonneg_left hphys (sq_nonneg V)
  have h2 := mul_le_mul_of_nonneg_left hdp (show 0 ≤ 3 * V ^ 3 + V ^ 2 by positivity)
  nlinarith

end OAI.Analysis.PDE.Elliptic
