import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogChartLowerBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TwoFormPointCoordinates

/-! # Log Global Lower Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogGlobalLowerBound

noncomputable section

/-! One proved global original Fubini--Study lower bound for the actual logarithmic point-potential family, independent of its small positive regularization parameter. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveLogPointPotential_global_lower_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hηx : η =ᶠ[𝓝 x] fun _ => 1) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
      ∀ (y : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) y), v ≠ 0 →
      -B * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re ≤
        ((Complex.I • ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε))
          y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re := by
  let bound := LogChartLowerBound.projectiveLogPointPotential_chart_lower_bound V e he η hη hc hs x hηx m
  refine ⟨bound.choose, bound.choose_spec.1, ?_⟩
  intro ε hε hε1 y v hv
  by_cases hy : y ∈ e.source
  · have hb := bound.choose_spec.2 ε hε hε1 (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e y hy)
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e y v))
    have hq : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y)
        ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e y v))
        ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e y v)) =
        (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re := by
      rw [ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric, ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply]
      change (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y)
        ![(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e y v),
          Complex.I • (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e y v)]).re = _
      exact congrArg Complex.re (TwoFormPointCoordinates.smoothForm_euclidean_at_point V (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V) e he y hy v)
    rw [hq,
      TwoFormPointCoordinates.smoothForm_euclidean_at_point V
        (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)) e he y hy v] at hb
    exact hb
  · change -bound.choose * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re ≤
      (Complex.I * ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)
        y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re
    rw [LogCurvatureSupport.projectiveLogPointPotential_curvature_zero_off_chart V e he η hη hc hs x m ε hε hy]
    change -bound.choose * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V y ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul y Complex.I v]).re ≤ (Complex.I * (0 : ℂ)).re
    simpa only [mul_zero, Complex.zero_re] using
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr bound.choose_spec.1.le)
        (ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_positive V y v hv).le

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogGlobalLowerBound
