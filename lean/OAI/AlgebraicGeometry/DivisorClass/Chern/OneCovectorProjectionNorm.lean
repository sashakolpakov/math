import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates

/-! # One Covector Projection Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm

noncomputable section

/-! The actual one-covector identification is isometric, and antiholomorphic projection is contractive. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneFormLinearEquiv_norm (q : E →L[ℝ] ℂ) : ‖AntiOneFormCoordinates.oneFormLinearEquiv q‖ = ‖q‖ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).norm_map q

theorem oneFormLinear_norm (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : ‖AntiOneFormCoordinates.oneFormLinear a‖ = ‖a‖ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).symm.norm_map a

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem complexAntilinearPart_covector_norm_le (q : E →L[ℝ] ℂ) :
    ‖Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ q‖ ≤ ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q)
  intro v
  have h1 := q.le_opNorm v
  have h2 := q.le_opNorm (Complex.I • v)
  simp only [norm_smul, Complex.norm_I, one_mul] at h2
  calc
    ‖Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ q v‖ = (1 / 2 : ℝ) * ‖q v + Complex.I • q (Complex.I • v)‖ := by
      rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖q v‖ + ‖q (Complex.I • v)‖) := by
      gcongr
      simpa only [norm_smul, Complex.norm_I, one_mul] using norm_add_le (q v) (Complex.I • q (Complex.I • v))
    _ ≤ ‖q‖ * ‖v‖ := by linarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm
