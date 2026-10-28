import OAI.Analysis.PDE.Dirichlet.RigidBoundary

open Set Filter
open scoped Topology

namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The artificial-boundary size of the affine derivative requires only
the first derivative bound already supplied by the global gradient estimate. -/
theorem affineDerivative_abs_bound {u : E → ℝ} (e : E) (A : E →L[ℝ] E)
    {x : E} {G R : ℝ} (hG : 0 ≤ G) (hu : ‖fderiv ℝ u x‖ ≤ G) (hx : ‖x‖ ≤ R) :
    |affineDerivative u e A x| ≤ G * (‖e‖ + ‖A‖ * R) := by
  have hfield : ‖e + A x‖ ≤ ‖e‖ + ‖A‖ * R := by
    calc
      _ ≤ ‖e‖ + ‖A x‖ := norm_add_le _ _
      _ ≤ ‖e‖ + ‖A‖ * ‖x‖ := add_le_add le_rfl (A.le_opNorm x)
      _ ≤ ‖e‖ + ‖A‖ * R := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx (norm_nonneg A))
  calc
    _ = ‖fderiv ℝ u x (e + A x)‖ := by simp only [affineDerivative, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ u x‖ * ‖e + A x‖ := (fderiv ℝ u x).le_opNorm _
    _ ≤ G * ‖e + A x‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _ ≤ G * (‖e‖ + ‖A‖ * R) := mul_le_mul_of_nonneg_left hfield hG

/-- The two-sided scalar barriers transfer any adapted tangential boundary
estimate for the defining function to the solution. -/
theorem affineDerivative_abs_le_of_barriers {u r : E → ℝ} {K : Set E}
    {x : E} {b B : ℝ} (e : E) (A : E →L[ℝ] E)
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (hbB : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K) :
    |affineDerivative u e A x| ≤ B * |affineDerivative r e A x| := by
  obtain ⟨a, hba, haB, ha⟩ := boundary_gradient_factor_of_barriers
    hu hr hux hrx hrne hb hbB hbarriers hnear
  have hapos : 0 ≤ a := hb.trans hba
  simp only [affineDerivative, ha, smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hapos]
  exact mul_le_mul_of_nonneg_right haB (abs_nonneg _)

/-- In particular, the quadratic defining-function estimate yields the
actual quadratic boundary data used in the mixed Hessian barrier. -/
theorem affineDerivative_quadratic_data_of_barriers {u r : E → ℝ} {K : Set E}
    {x : E} {b B C : ℝ} (e : E) (A : E →L[ℝ] E)
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (hbB : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K)
    (hquad : |affineDerivative r e A x| ≤ C * ‖x‖ ^ 2) :
    |affineDerivative u e A x| ≤ (B * C) * ‖x‖ ^ 2 := by
  have h := affineDerivative_abs_le_of_barriers e A hu hr hux hrx hrne hb hbB hbarriers hnear
  have hB : 0 ≤ B := hb.trans hbB
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hB)

end OAI.Analysis.PDE.Dirichlet
