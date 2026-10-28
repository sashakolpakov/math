import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Affine

/-! Returning a local Hessian Hölder estimate to the original coordinates. -/

noncomputable section
open Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem hessian_holder_of_dilate {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (x₀ : EuclideanSpace ℝ (Fin m)) {r s α C : ℝ} (hr : 0 < r) (hs : 0 < s) (hC : 0 < C)
    (hh : ∀ x ∈ ball 0 s, ∀ y ∈ ball 0 s,
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + r • z))) x -
        fderiv ℝ (fderiv ℝ (fun z => u (x₀ + r • z))) y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ D > 0, ∀ x ∈ ball x₀ (r * s), ∀ y ∈ ball x₀ (r * s),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ D * ‖x - y‖ ^ α := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    r⁻¹ • ContinuousLinearMap.id ℝ _
  let v := fun z => u (x₀ + r • z)
  let inv := fun z => r⁻¹ • (z - x₀)
  have hpoint (z : EuclideanSpace ℝ (Fin m)) : x₀ + r • inv z = z := by
    dsimp [inv]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hinv (z) (hz : z ∈ ball x₀ (r * s)) : inv z ∈ ball 0 s := by
    change ‖r⁻¹ • (z - x₀) - 0‖ < s
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hz' : ‖z - x₀‖ < r * s := by simpa only [mem_ball, dist_eq_norm] using hz
    calc
      _ < r⁻¹ * (r * s) := mul_lt_mul_of_pos_left hz' (inv_pos.mpr hr)
      _ = s := by field_simp
  have hD (z a b : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fderiv ℝ v) (inv z) (L a) (L b) = fderiv ℝ (fderiv ℝ u) z a b := by
    have h := second_fderiv_comp_affine u hu (r • ContinuousLinearMap.id ℝ _) x₀ (inv z) (L a) (L b)
    simp only [smul_apply, ContinuousLinearMap.id_apply] at h
    change fderiv ℝ (fderiv ℝ v) (inv z) (L a) (L b) = _ at h
    rw [hpoint] at h
    dsimp [L] at h
    simpa only [L, smul_apply, ContinuousLinearMap.id_apply,
      smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h
  let D := C * ‖L‖ ^ 2 * |r⁻¹| ^ α + 1
  have hDpos : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hDpos, ?_⟩
  intro x hx y hy
  have hnorm := bilinear_norm_le_pullback
    (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
    (fderiv ℝ (fderiv ℝ v) (inv x) - fderiv ℝ (fderiv ℝ v) (inv y)) L (by
      intro a b
      simp only [sub_apply, hD])
  have hdist : ‖inv x - inv y‖ = |r⁻¹| * ‖x - y‖ := by
    have he : inv x - inv y = r⁻¹ • (x - y) := by dsimp [inv]; rw [← smul_sub]; congr 1; abel
    rw [he, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ v) (inv x) - fderiv ℝ (fderiv ℝ v) (inv y)‖ * ‖L‖ ^ 2 := hnorm
    _ ≤ (C * ‖inv x - inv y‖ ^ α) * ‖L‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hh _ (hinv x hx) _ (hinv y hy)) (sq_nonneg _)
    _ = (C * ‖L‖ ^ 2 * |r⁻¹| ^ α) * ‖x - y‖ ^ α := by
      rw [hdist, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      ring
    _ ≤ D * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
      (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Schauder
