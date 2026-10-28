import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.WeightedTransition
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorDivergence

/-! # Tensor Transition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Original covariant tensor energy and flux are independent of the line frame in a fixed projective chart. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorPair (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (h.projectiveWeightChart V e i z *
    CovectorTensorAlgebra.covectorTensorMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
      (Line.RoughAnti.lineCovectorAntiDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension) z)
      (Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension) z))

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorFlux (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace)
    (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  Line.TensorMetricTest.lineTensorFlux (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (Line.RoughAnti.lineCovectorAntiDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension))
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension) k z

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorPair_transition
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    h.projectiveFrameTensorPair V e U n a c j z = h.projectiveFrameTensorPair V e U n a c i z := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorPair Line.RoughAnti.lineCovectorAntiDerivative
  rw [h.projectiveAntiDerivative_transition V e he U n a i j hz,
    h.projectiveCovectorDerivative_transition V e he U n c i j hz]
  rw [TensorMetricRe.covectorTensorMetricPair_weighted_gauge _ n _ _ _ _ _ _
    (h.projectiveWeightChart_transition V e i j ⟨hz.1, hz.2.2⟩)]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorFlux_transition
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i j : V.analyticSpace) (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    h.projectiveFrameTensorFlux V e U n a c j k z = h.projectiveFrameTensorFlux V e U n a c i k z := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorFlux Line.TensorMetricTest.lineTensorFlux Line.RoughAnti.lineCovectorAntiDerivative
  rw [h.projectiveAntiDerivative_transition V e he U n a i j hz,
    Projective.FrameScalarGlue.holomorphicLineSmoothForm_transition_chart V u e U n c i j hz]
  simp only [_root_.smul_apply]
  rw [TensorMetricRe.bilinearFormMetricPair_weighted_gauge _ n _ _ _ _ _ _
    (h.projectiveWeightChart_transition V e i j ⟨hz.1, hz.2.2⟩)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
