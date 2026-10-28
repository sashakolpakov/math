import OAI.Analysis.PDE.Schauder.Dirichlet.HalfspaceLowerJets

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Schauder

/-- On a closed halfspace, all lower jets can be absorbed into an
arbitrarily small multiple of the top Hölder seminorm. No norm of an
extension outside the halfspace enters the estimate. -/
theorem halfspace_lower_jet_interpolation {m : ℕ} (k : Fin m) {α ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      (∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε * H + B * M) ∧
      (∀ x, 0 ≤ x k → ‖fderiv ℝ u x‖ ≤ ε * H + B * M) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        |u x-u y| ≤ (ε * H + B * M) * ‖x-y‖ ^ α) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ (ε * H + B * M) * ‖x-y‖ ^ α) := by
  let c : ℝ := 1 + 2 * m
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨B₀, hB₀, hinterp⟩ := halfspace_hessian_interpolation k hα (div_pos hε hc)
  let B : ℝ := c * B₀ + 4 * m + 3
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro u hu huc H M hH hM hbound hh
  let D := (ε / c) * H + B₀ * M
  let G : ℝ := m * (D + 2 * M)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hHess : ∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ D :=
    hinterp u hu huc H M hH hM hbound hh
  have hGrad : ∀ x, 0 ≤ x k → ‖fderiv ℝ u x‖ ≤ G :=
    halfspace_gradient_bound k hu hD hM hHess hbound
  have hcore : c * D = ε * H + c * B₀ * M := by
    dsimp [D]
    field_simp

  have hDle : D ≤ ε * H + B * M := by
    have hc1 : 1 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hmul := mul_le_mul_of_nonneg_right hc1 hD
    dsimp [B]
    nlinarith
  have hGG : G ≤ ε * H + B * M := by
    have hm : (m : ℝ) ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hmul := mul_le_mul_of_nonneg_right hm hD
    dsimp [G, B]
    nlinarith
  have hFU : G + 2*M ≤ ε * H + B*M := by
    have hm : (m : ℝ) ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hmul := mul_le_mul_of_nonneg_right hm hD
    dsimp [G, B]
    nlinarith
  have hDG : D + 2*G ≤ ε * H + B*M := by
    have heq : D + 2*G = c*D + 4*m*M := by dsimp [G, c]; ring
    rw [heq, hcore]
    dsimp [B]
    nlinarith
  have hLipU : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → |u x-u y| ≤ G * ‖x-y‖ := by
    intro x hx y hy
    simpa only [Real.norm_eq_abs] using
      (convex_coordinate_halfspace k).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ hu.differentiable (by norm_num) z) hGrad hy hx
  have hHolderU := halfspace_holder_of_bounded_lipschitz k u hα.le hα1 hM hG
    (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hbound x hx)
    (fun x hx y hy ↦ by simpa only [Real.norm_eq_abs] using hLipU x hx y hy)
  have hHolderD := halfspace_holder_of_bounded_lipschitz k (fderiv ℝ u) hα.le hα1 hG hD
    hGrad (halfspace_fderiv_lipschitz k hu hHess)
  refine ⟨fun x hx ↦ (hHess x hx).trans hDle, fun x hx ↦ (hGrad x hx).trans hGG, ?_, ?_⟩
  · intro x hx y hy
    have h := hHolderU x hx y hy
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right hFU (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    exact (hHolderD x hx y hy).trans
      (mul_le_mul_of_nonneg_right hDG (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
