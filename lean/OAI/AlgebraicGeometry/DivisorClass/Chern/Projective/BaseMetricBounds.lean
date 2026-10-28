import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseActionBounds
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricBound

/-! # Base Metric Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseMetricBounds

noncomputable section

/-! The actual base-curvature contribution is bounded in the original metric pairing, uniformly on compact projective chart sets. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] BaseActionBounds.baseBound_sharpNormed BaseActionBounds.baseBound_sharpSpace

local instance basePair_metricNormed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedAddCommGroup (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) := inferInstance
local instance basePair_metricSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    NormedSpace ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) := inferInstance

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveBaseCurvatureAction_pair_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      |(Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B
        (BaseCurvatureAction.baseCurvatureAction b B (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z a) a).re| ≤
        C * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  obtain ⟨R, hR, hbase⟩ := BaseActionBounds.projectiveBaseCurvatureAction_bound V e he hT hTD
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
  have hc : ContinuousOn (fun z => 2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)‖ * R *
      ‖ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z‖) T :=
    ((continuousOn_const.mul ((hS.continuousOn.mono hTD).norm)).mul continuousOn_const).mul
      (((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).continuousOn.mono hTD).norm)
  obtain ⟨Q, hQ⟩ := hT.bddAbove_image hc
  refine ⟨max Q 0 + 1, by positivity, ?_⟩
  intro z hz a
  have hp := OneCovectorMetricBound.oneCovectorMetric_pair_control (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz)) a _ R hR.le (hbase z hz a)
  apply hp.trans
  apply mul_le_mul_of_nonneg_right
    ((hQ ⟨z, hz, rfl⟩).trans ((le_max_left Q 0).trans (by linarith)))
  rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic _ 1 _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz))]
  exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg 1 _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseMetricBounds
