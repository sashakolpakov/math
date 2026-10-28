import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem convex_closedHalfBall (v : E) : Convex ℝ (closedHalfBall v) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have hx' : x ∈ Metric.closedBall (0 : E) 1 := by simpa using hx.1
    have hy' : y ∈ Metric.closedBall (0 : E) 1 := by simpa using hy.1
    simpa using (convex_closedBall (0 : E) 1) hx' hy' ha hb hab
  · simpa [inner_add_right, real_inner_smul_right] using
      add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- A gradient bound and zero flat-boundary data give the two-sided linear
slope bound required by the boundary oscillation theorem. -/
theorem boundary_slope_of_gradient (v : E) (hv : ‖v‖ = 1) {u : E → ℝ} {G : ℝ}
    (hu : ∀ x ∈ closedHalfBall v, DifferentiableAt ℝ u x)
    (hgrad : ∀ x ∈ closedHalfBall v, ‖fderiv ℝ u x‖ ≤ G)
    (hzero : ∀ x, ‖x‖ ≤ 1 → inner ℝ v x = 0 → u x = 0) :
    ∀ x ∈ closedHalfBall v, (-G) * inner ℝ v x ≤ u x ∧ u x ≤ G * inner ℝ v x := by
  intro x hx
  let z := x - (inner ℝ v x) • v
  have hz : ‖z‖ ≤ 1 := (norm_tangential_part_le v x hv).trans hx.1
  have hperp : inner ℝ v z = 0 := by
    simp [z, inner_sub_right, real_inner_smul_right, hv]
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le hu hgrad (convex_closedHalfBall v)
    (show z ∈ closedHalfBall v from ⟨hz, by simp [hperp]⟩) hx
  have he : x - z = (inner ℝ v x) • v := by dsimp only [z]; abel
  rw [hzero z hz hperp, sub_zero, Real.norm_eq_abs, he, norm_smul, hv, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hx.2] at hb
  exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

end OAI.Analysis.PDE.Elliptic
