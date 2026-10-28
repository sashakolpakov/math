import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorTransition
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricSmooth

/-! # Tensor Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual frame tensor energy and flux are smooth on their original projective domains. -/

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

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveAntiDerivative_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞
      (Line.RoughAnti.lineCovectorAntiDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension))
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
  ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)).restrictScalars ℝ).contDiff.comp_contDiffOn
    (h.projectiveCovectorConnection_smooth V e he U n a i)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorPair_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveFrameTensorPair V e U n a c i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  have hp := TensorMetricSmooth.covectorTensorMetricPair_smoothOn
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) _ _
    D.isOpen ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hz => hz.1))
    (h.projectiveAntiDerivative_smooth V e he U n a i)
    (h.projectiveCovectorConnection_smooth V e he U n c i)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)
  have hw : ContDiffOn ℝ ∞ (h.projectiveWeightChart V e i) (D : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    (h.projectiveWeightChart_smooth V e he i).mono (fun _ hz => ⟨hz.1, hz.2.2⟩)
  have hρ : ContDiffOn ℝ ∞ (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e) (D : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).mono (fun _ hz => hz.1)
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hρ).mul (hw.mul hp)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorFlux_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace)
    (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ContDiffOn ℝ ∞ (h.projectiveFrameTensorFlux V e U n a c i k)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  apply TensorMetricSmooth.lineTensorFlux_smoothOn
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (h.projectiveWeightChart V e i) _ _
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
  · exact (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hz => hz.1)
  · exact (h.projectiveWeightChart_smooth V e he i).mono (fun _ hz => ⟨hz.1, hz.2.2⟩)
  · exact h.projectiveAntiDerivative_smooth V e he U n a i
  · exact ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he _ n (c.val i)
  · exact fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1
  · exact fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
