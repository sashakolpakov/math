import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureNorm
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

/-! # Mixed Curvature Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.MixedCurvatureNorm

noncomputable section

/-! The additional mixed curvature trace is a bounded zeroth-order operator on original covectors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace
  Line.CurvatureNorm.curvatureNorm_covectorNormed Line.CurvatureNorm.curvatureNorm_covectorSpace Line.CurvatureNorm.curvatureNorm_covectorComplex
  Line.CurvatureNorm.curvatureNorm_twoNormed Line.CurvatureNorm.curvatureNorm_twoSpace Line.CurvatureNorm.curvatureNorm_formComplex

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]

local instance mixedCurv_baseEndNormed : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance mixedCurv_baseEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance mixedCurv_actionNormed (n : ℕ) :
    NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance mixedCurv_actionSpace (n : ℕ) :
    NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem lineCovectorCurvatureValue_norm (n : ℕ) (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    {C : ℝ} (hR : ∀ v w, ‖R v w‖ ≤ C * ‖v‖ * ‖w‖) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (v w : E) :
    ‖-Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R v w) a + F ![v, w] • a‖ ≤
      (‖Line.CovectorConnectionOperator.covectorActionOperator (E := E) n‖ * C + ‖AntiTwoFormCoefficients.twoFormBilinear F‖) * ‖v‖ * ‖w‖ * ‖a‖ := by
  have hc : ‖Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R v w) a‖ ≤
      ‖Line.CovectorConnectionOperator.covectorActionOperator (E := E) n‖ * (C * ‖v‖ * ‖w‖) * ‖a‖ :=
    ((Line.CovectorConnectionOperator.covectorActionOperator n (R v w)).le_opNorm a).trans
      ((mul_le_mul_of_nonneg_right ((Line.CovectorConnectionOperator.covectorActionOperator n).le_opNorm (R v w)) (norm_nonneg a)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hR v w) (norm_nonneg _)) (norm_nonneg a)))
  have hf : ‖F ![v, w] • a‖ ≤ (‖AntiTwoFormCoefficients.twoFormBilinear F‖ * ‖v‖ * ‖w‖) * ‖a‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (Line.CurvatureNorm.twoFormBilinear_eval_norm F v w) (norm_nonneg a)
  calc
    _ ≤ ‖Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R v w) a‖ + ‖F ![v, w] • a‖ := by
      simpa only [norm_neg] using norm_add_le (-Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R v w) a) (F ![v, w] • a)
    _ ≤ _ := (add_le_add hc hf).trans_eq (by ring)

variable [NormedSpace ℂ E]

theorem lineCovectorMixedCurvatureTrace_norm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    {C : ℝ} (hR : ∀ v w, ‖R v w‖ ≤ C * ‖v‖ * ‖w‖) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    ‖Line.RoughAnti.lineCovectorMixedCurvatureTrace b n B R F a‖ ≤
      ((‖Line.CovectorConnectionOperator.covectorActionOperator (E := E) n‖ * C + ‖AntiTwoFormCoefficients.twoFormBilinear F‖) *
        ∑ j, ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖) * ‖a‖ := by
  unfold Line.RoughAnti.lineCovectorMixedCurvatureTrace
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, ((‖Line.CovectorConnectionOperator.covectorActionOperator (E := E) n‖ * C + ‖AntiTwoFormCoefficients.twoFormBilinear F‖) * ‖b j‖ *
        ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖ * ‖a‖) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_smul, Complex.norm_I, one_mul] using
        lineCovectorCurvatureValue_norm n R F hR a (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.MixedCurvatureNorm
