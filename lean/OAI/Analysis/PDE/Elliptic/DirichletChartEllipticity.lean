import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanChartEquation
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Quantitative ellipticity under a fixed chart. Both Jacobians enter
only through their uniform norm bounds. -/
theorem pullbackEllipticOperator_uniform_bounds (J D A : E →L[ℝ] E)
    (hinv : J.comp D = ContinuousLinearMap.id ℝ E)
    {C ell Λ : ℝ} (hC : 0 < C) (hJ : ‖J‖ ≤ C) (hD : ‖D‖ ≤ C)
    (hell : 0 ≤ ell) (hΛ : 0 ≤ Λ)
    (hlo : ∀ v : E, ell * ‖v‖^2 ≤ inner ℝ v (A v))
    (hhi : ∀ v : E, inner ℝ v (A v) ≤ Λ * ‖v‖^2) (v : E) :
    (ell / C^2) * ‖v‖^2 ≤ inner ℝ v (pullbackEllipticOperator J A v) ∧
      inner ℝ v (pullbackEllipticOperator J A v) ≤ (Λ * C^2) * ‖v‖^2 := by
  have hadj : D.adjoint.comp J.adjoint = ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, hinv, ContinuousLinearMap.adjoint_id]
  have hnormlo : ‖v‖ ≤ C * ‖J.adjoint v‖ := by
    have he : D.adjoint (J.adjoint v) = v :=
      congrArg (fun T : E →L[ℝ] E => T v) hadj
    calc
      _ = ‖D.adjoint (J.adjoint v)‖ := congrArg norm he.symm
      _ ≤ ‖D.adjoint‖ * ‖J.adjoint v‖ := D.adjoint.le_opNorm _
      _ ≤ C * ‖J.adjoint v‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr
  have hnormhi : ‖J.adjoint v‖ ≤ C * ‖v‖ := by
    apply (J.adjoint.le_opNorm v).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right hJ (norm_nonneg v)
  have hslo : ‖v‖^2 ≤ C^2 * ‖J.adjoint v‖^2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg v) hnormlo]
  have hshi : ‖J.adjoint v‖^2 ≤ C^2 * ‖v‖^2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg (J.adjoint v)) hnormhi]
  rw [pullbackEllipticOperator_form]
  constructor
  · calc
      _ = (ell * ‖v‖^2) / C^2 := by ring
      _ ≤ ell * ‖J.adjoint v‖^2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hC)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hslo hell]
      _ ≤ _ := hlo _
  · exact (hhi _).trans ((mul_le_mul_of_nonneg_left hshi hΛ).trans_eq (by ring))

end OAI.Analysis.PDE.Elliptic
