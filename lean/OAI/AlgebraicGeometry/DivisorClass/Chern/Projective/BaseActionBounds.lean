import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureActionNorm
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCurvatureBounds

/-! # Base Action Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseActionBounds

noncomputable section

/-! The original base-curvature action has a uniform operator bound on compact projective chart sets, independent of all line metrics and twists. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance baseBound_sharpNormed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedAddCommGroup ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) := inferInstance
local instance baseBound_sharpSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedSpace ℝ ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) := inferInstance

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveBaseCurvatureAction_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      ‖BaseCurvatureAction.baseCurvatureAction (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z a‖ ≤ C * ‖a‖ := by
  obtain ⟨R, hR, hcurv⟩ := BaseCurvatureBounds.projectiveBaseConnectionCurvature_bound V e he hT hTD
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
  have hSi (i) : ContDiffOn ℝ ∞
      (fun z => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (b.coord i).toContinuousLinearMap)
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    (ContinuousLinearMap.apply ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (b.coord i).toContinuousLinearMap).contDiff.comp_contDiffOn hS
  have hc : ContinuousOn (fun z => R * ∑ i, ‖b i‖ *
      ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (b.coord i).toContinuousLinearMap‖) T := by
    apply continuousOn_const.mul
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact continuousOn_const.mul (((hSi i).continuousOn.mono hTD).norm)
  obtain ⟨Q, hQ⟩ := hT.bddAbove_image hc
  refine ⟨max Q 0 + 1, by positivity, ?_⟩
  intro z hz a
  have hr := BaseCurvatureActionNorm.baseCurvatureAction_norm_le b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z R hR.le (fun v w => hcurv z hz v w) a
  apply hr.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
  exact (hQ ⟨z, hz, rfl⟩).trans ((le_max_left Q 0).trans (by linarith))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseActionBounds
