import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Unnormalize

/-! Quantitative return from a linear coordinate change.
The constant stays linear in the supplied Hölder bound. -/

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem fullspace_hessian_holder_of_affine {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin m))
    {s α H N : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hN : 0 ≤ N) (hLn : ‖L.symm.toContinuousLinearMap‖ ≤ N)
    (hh : ∀ x ∈ ball 0 s, ∀ y ∈ ball 0 s,
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + L z))) x -
        fderiv ℝ (fderiv ℝ (fun z => u (x₀ + L z))) y‖ ≤ H * ‖x - y‖ ^ α) :
    ∀ x ∈ ball x₀ (s / (N + 1)),
      ∀ y ∈ ball x₀ (s / (N + 1)),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        (N ^ 2 * N ^ α) * H * ‖x - y‖ ^ α := by
  let v := fun z => u (x₀ + L z)
  let inv := fun z => L.symm (z - x₀)
  have hpoint (z : EuclideanSpace ℝ (Fin m)) : x₀ + L (inv z) = z := by
    dsimp only [inv]
    rw [L.apply_symm_apply]
    abel
  have hinv (z) (hz : z ∈ ball x₀ (s / (N + 1))) : inv z ∈ ball 0 s := by
    change ‖inv z - 0‖ < s
    rw [sub_zero]
    have hz' : ‖z - x₀‖ < s / (N + 1) := by simpa only [mem_ball, dist_eq_norm] using hz
    calc
      _ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖z - x₀‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ N * ‖z - x₀‖ := mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ ≤ (N + 1) * ‖z - x₀‖ := by nlinarith [norm_nonneg (z - x₀)]
      _ < (N + 1) * (s / (N + 1)) := mul_lt_mul_of_pos_left hz' (by positivity)
      _ = s := by field_simp
  have hD (z a b : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fderiv ℝ v) (inv z) (L.symm a) (L.symm b) =
        fderiv ℝ (fderiv ℝ u) z a b := by
    have h := second_fderiv_comp_affine u hu L.toContinuousLinearMap x₀ (inv z) (L.symm a) (L.symm b)
    change fderiv ℝ (fderiv ℝ v) (inv z) (L.symm a) (L.symm b) =
      fderiv ℝ (fderiv ℝ u) (x₀ + L (inv z)) (L (L.symm a)) (L (L.symm b)) at h
    simpa only [hpoint, L.apply_symm_apply] using h
  intro x hx y hy
  have hnorm := bilinear_norm_le_pullback
    (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
    (fderiv ℝ (fderiv ℝ v) (inv x) - fderiv ℝ (fderiv ℝ v) (inv y)) L.symm.toContinuousLinearMap (by
      intro a b
      simp only [sub_apply, ContinuousLinearEquiv.coe_coe, hD])
  have hdist : ‖inv x - inv y‖ ≤ N * ‖x - y‖ := by
    have he : inv x - inv y = L.symm (x - y) := by
      dsimp only [inv]
      rw [← map_sub]
      congr 1
      abel
    rw [he]
    exact (L.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hLn (norm_nonneg _))
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ v) (inv x) - fderiv ℝ (fderiv ℝ v) (inv y)‖ *
        ‖L.symm.toContinuousLinearMap‖ ^ 2 := hnorm
    _ ≤ (H * ‖inv x - inv y‖ ^ α) * N ^ 2 := by
      apply mul_le_mul (hh _ (hinv x hx) _ (hinv y hy))
      · exact pow_le_pow_left₀ (norm_nonneg _) hLn 2
      · positivity
      · positivity
    _ ≤ (H * (N * ‖x - y‖) ^ α) * N ^ 2 := by
      gcongr
    _ = _ := by rw [Real.mul_rpow hN (norm_nonneg _)]; ring

end OAI.Analysis.PDE.Schauder
