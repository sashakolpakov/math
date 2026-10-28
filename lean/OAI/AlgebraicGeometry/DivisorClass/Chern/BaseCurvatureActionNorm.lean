import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm

/-! # Base Curvature Action Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureActionNorm

noncomputable section

/-! The actual base-curvature action is bounded independently of the line metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] BaseCurvatureAction.baseAction_endNormed BaseCurvatureAction.baseAction_endSpace
  BaseCurvatureAction.baseAction_directionNormed BaseCurvatureAction.baseAction_directionSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem baseCurvatureAction_norm_le (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ v w : E, ‖OperatorConnectionCurvature.operatorConnectionCurvature G x v w‖ ≤ C * ‖v‖ * ‖w‖)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    ‖BaseCurvatureAction.baseCurvatureAction b B G x a‖ ≤
      (C * ∑ i, ‖b i‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap‖) * ‖a‖ := by
  rw [BaseCurvatureAction.baseCurvatureAction, OneCovectorProjectionNorm.oneFormLinearEquiv_norm]
  apply (OneCovectorProjectionNorm.complexAntilinearPart_covector_norm_le _).trans
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [BaseCurvatureAction.baseCurvatureContraction_apply, norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w) a)
        (fun _ => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)‖) ≤
      ∑ i, ‖a‖ * (C * ‖b i‖ * ‖w‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [OneCovectorCurvature.covectorInfinitesimalAction_one_apply, ← AntiOneFormCoordinates.oneFormLinear_apply]
      calc
        _ ≤ ‖AntiOneFormCoordinates.oneFormLinear a‖ * ‖OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w
            (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)‖ := (AntiOneFormCoordinates.oneFormLinear a).le_opNorm _
        _ ≤ ‖a‖ * (‖OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w‖ *
            ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap‖) := by
          rw [OneCovectorProjectionNorm.oneFormLinear_norm]
          gcongr
          exact (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w).le_opNorm _
        _ ≤ _ := by
          gcongr
          exact hR (b i) w
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureActionNorm
