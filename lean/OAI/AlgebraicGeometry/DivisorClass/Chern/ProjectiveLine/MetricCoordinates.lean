import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.Kahler
import OAI.AlgebraicGeometry.DivisorClass.Chern.MetricConnectionCoordinates

/-! # Metric Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual line metric and its compatibility equation in the original projective Euclidean coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (h.weightFunction i) (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart_apply (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveWeightChart V e i z = (h.weight i ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩ : ℂ) :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply _ (h.weightFunction i) ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart_smooth (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveWeightChart V e i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
  (SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff (h.weightFunction i) e he).comp
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn (fun _ hz => hz)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart_derivative (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (h.projectiveWeightChart V e i) z v = h.projectiveWeightChart V e i z *
      (conj (h.projectiveConnectionChart V e i z v) + h.projectiveConnectionChart V e i z v) := by
  let w := Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (h.weightFunction i) ∘ e.symm
  have hw := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff (h.weightFunction i) e he).contDiffAt
    ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hd := hw.hasFDerivAt.comp z
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hv := congrArg (fun L : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (h.projectiveWeightChart V e i) z v =
    fderiv ℝ w (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v) at hv
  exact hv.trans (h.weightFunction_chart_derivative i e he hz (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
