import OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure

/-! # Metric Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint

noncomputable section

/-! The constructed scalar codifferential uses exactly the original metric measure:
the two local and global measure constructions are proved equal. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction
attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveChartMeasure_eq_variety
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure V e = ComplexMultiplication.HodgeComparison.MetricChartMeasure.CM.Construction.varietyMetricChartMeasure V e := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveChartMeasure_lintegral V e he f hf, ComplexMultiplication.HodgeComparison.MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_lintegral V e he f hf]

theorem projectiveMetricVolume_eq_variety : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V = ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  apply ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure_unique
  intro e he
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume_restrict V e he, projectiveChartMeasure_eq_variety V e he,
    ComplexMultiplication.HodgeComparison.MetricChartMeasure.CM.Construction.varietyMetricChartMeasure_restrict_source]

theorem projectiveL2Pair_actualMetricIntegral (n : ℕ)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n a b =
      ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  unfold Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair
  rw [projectiveMetricVolume_eq_variety]

theorem projectiveCodifferential_actualMetricIntegral (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V n b).val a.val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  rw [← projectiveL2Pair_actualMetricIntegral, ← projectiveL2Pair_actualMetricIntegral]
  exact Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair V n a b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint
