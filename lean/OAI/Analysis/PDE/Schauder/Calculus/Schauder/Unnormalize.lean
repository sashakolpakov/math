import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Congruence

/-! Pulling a genuine local Hölder Hessian estimate back through a linear isomorphism. -/

noncomputable section
open Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem hessian_holder_of_affine {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin m)) {s α C : ℝ}
    (hs : 0 < s) (hα : 0 ≤ α) (hC : 0 < C)
    (hh : ∀ x ∈ ball 0 s, ∀ y ∈ ball 0 s,
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + L z))) x -
        fderiv ℝ (fderiv ℝ (fun z => u (x₀ + L z))) y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ r > 0, ∃ D > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ D * ‖x - y‖ ^ α := by
  let N := ‖L.symm.toContinuousLinearMap‖
  have hN : 0 ≤ N := norm_nonneg _
  let r := s / (N + 1)
  have hr : 0 < r := div_pos hs (by positivity)
  let v := fun z => u (x₀ + L z)
  let inv := fun z => L.symm (z - x₀)
  have hpoint (z : EuclideanSpace ℝ (Fin m)) : x₀ + L (inv z) = z := by
    dsimp only [inv]
    rw [L.apply_symm_apply]
    abel
  have hinv (z) (hz : z ∈ ball x₀ r) : inv z ∈ ball 0 s := by
    change ‖inv z - 0‖ < s
    rw [sub_zero]
    have hz' : ‖z - x₀‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
    calc
      _ ≤ N * ‖z - x₀‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (N + 1) * ‖z - x₀‖ := by nlinarith [norm_nonneg (z - x₀)]
      _ < (N + 1) * r := mul_lt_mul_of_pos_left hz' (by positivity)
      _ = s := by dsimp only [r]; field_simp
  have hD (z a b : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fderiv ℝ v) (inv z) (L.symm a) (L.symm b) =
        fderiv ℝ (fderiv ℝ u) z a b := by
    have h := second_fderiv_comp_affine u hu L.toContinuousLinearMap x₀ (inv z) (L.symm a) (L.symm b)
    change fderiv ℝ (fderiv ℝ v) (inv z) (L.symm a) (L.symm b) =
      fderiv ℝ (fderiv ℝ u) (x₀ + L (inv z)) (L (L.symm a)) (L (L.symm b)) at h
    simpa only [hpoint, L.apply_symm_apply] using h
  let D := C * N ^ 2 * N ^ α + 1
  have hDpos : 0 < D := by dsimp only [D]; positivity
  refine ⟨r, hr, D, hDpos, ?_⟩
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
    exact L.symm.toContinuousLinearMap.le_opNorm _
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ v) (inv x) - fderiv ℝ (fderiv ℝ v) (inv y)‖ * N ^ 2 := hnorm
    _ ≤ (C * ‖inv x - inv y‖ ^ α) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (hh _ (hinv x hx) _ (hinv y hy)) (sq_nonneg _)
    _ ≤ (C * (N * ‖x - y‖) ^ α) * N ^ 2 := by
      gcongr
    _ = (C * N ^ 2 * N ^ α) * ‖x - y‖ ^ α := by
      rw [Real.mul_rpow hN (norm_nonneg _)]
      ring
    _ ≤ D * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith)
      (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Schauder
