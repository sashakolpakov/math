import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureContraction
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm

/-! # Curvature Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureNorm

noncomputable section

/-! Operator norm bounds for the original line-curvature action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]

local instance curvatureNorm_covectorNormed : NormedAddCommGroup (E →L[ℝ] ℂ) := inferInstance
local instance curvatureNorm_covectorSpace : NormedSpace ℝ (E →L[ℝ] ℂ) := inferInstance
local instance curvatureNorm_covectorComplex : NormedSpace ℂ (E →L[ℝ] ℂ) := inferInstance
local instance curvatureNorm_twoNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
local instance curvatureNorm_twoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
local instance curvatureNorm_formComplex (n : ℕ) : NormedSpace ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem twoFormBilinear_eq_native (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : AntiTwoFormCoefficients.twoFormBilinear F = ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear F := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact (AntiTwoFormCoefficients.twoFormBilinear_apply F v w).trans (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply F v w).symm

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem twoFormBilinear_continuous : Continuous (AntiTwoFormCoefficients.twoFormBilinear (E := E)) := by
  have heq : AntiTwoFormCoefficients.twoFormBilinear (E := E) = ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear := funext twoFormBilinear_eq_native
  rw [heq]
  exact (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear (E := E)).continuous

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem twoFormBilinear_eval_norm (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (v w : E) :
    ‖F ![v, w]‖ ≤ ‖AntiTwoFormCoefficients.twoFormBilinear F‖ * ‖v‖ * ‖w‖ := by
  rw [← AntiTwoFormCoefficients.twoFormBilinear_apply]
  exact ((AntiTwoFormCoefficients.twoFormBilinear F v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right ((AntiTwoFormCoefficients.twoFormBilinear F).le_opNorm v) (norm_nonneg w))

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem lineCurvatureAction_norm_le (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    ‖CurvatureContraction.lineCurvatureAction b B F a‖ ≤
      (‖AntiTwoFormCoefficients.twoFormBilinear F‖ * ∑ j, ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖) * ‖a‖ := by
  rw [CurvatureContraction.lineCurvatureAction, OneCovectorProjectionNorm.oneFormLinearEquiv_norm]
  apply (OneCovectorProjectionNorm.complexAntilinearPart_covector_norm_le _).trans
  rw [CurvatureContraction.lineCurvatureContraction]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) • AntiTwoFormCoefficients.twoFormBilinear F (b j)‖) ≤
        ∑ j, (‖a‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖) * (‖AntiTwoFormCoefficients.twoFormBilinear F‖ * ‖b j‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      have hq := (AntiOneFormCoordinates.oneFormLinear a).le_opNorm (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)
      rw [OneCovectorProjectionNorm.oneFormLinear_norm] at hq
      exact mul_le_mul hq ((AntiTwoFormCoefficients.twoFormBilinear F).le_opNorm (b j)) (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureNorm
