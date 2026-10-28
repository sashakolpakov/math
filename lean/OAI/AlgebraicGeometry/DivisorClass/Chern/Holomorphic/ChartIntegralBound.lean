import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartIntegrability
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates

/-! # Chart Integral Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Local norms of original bundle forms are integrable and bounded by their original global metric norm. -/

open _root_.MeasureTheory
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_integrable (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    IntegrableOn (fun z => (h.projectiveGlobalPair V e n a a z).re) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
  have hi : Integrable (fun x => (h.globalFormPair V n a a x).re) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) := by
    rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
    exact (h.globalFormPair_integrable V n a a).re
  simpa only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, smul_eq_mul] using
      Projective.ChartIntegrability.projective_chart_density_integrable V e he (fun x => (h.globalFormPair V n a a x).re) hi

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_integral_le (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {S : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hS : S ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ z in S, (h.projectiveGlobalPair V e n a a z).re) ≤ (h.formIntegralPair V n a a).re := by
  have hi : Integrable (fun x => (h.globalFormPair V n a a x).re) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) := by
    rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
    exact (h.globalFormPair_integrable V n a a).re
  have hb := Projective.ChartIntegrability.projective_chart_integral_le V e he (fun x => (h.globalFormPair V n a a x).re) hi
    (h.globalFormPair_nonneg V n a) hS
  rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V, ← h.formIntegralPair_re V n a a] at hb
  simpa only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
