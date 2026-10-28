import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorIntegration

/-! # Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Full covariant energy integration for the original projective metric and actual line connection. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullEnergy_integrable (n : ℕ) (i : V.analyticSpace)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hs : tsupport a ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Integrable (Line.RoughDivergence.lineCovectorFullEnergy (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (h.projectiveWeightChart V e i) a) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughDivergence.lineCovectorFullEnergy_integrable volume _ n _ _ _ _ a D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i) ha hac hs
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullRoughLaplacian_integral_pair (n : ℕ) (i : V.analyticSpace)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hs : tsupport a ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let w := h.projectiveWeightChart V e i
    (∫ x, Line.TensorMetricTest.lineMetricTestPair b n B w (Line.RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) a x) =
      ∫ x, Line.RoughDivergence.lineCovectorFullEnergy b n B G A w a x := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughDivergence.lineCovectorFullRoughLaplacian_integral_pair volume _ n _ _ _ _ a D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i) ha hac hs
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hx.1)
    (fun _ hx => h.projectiveWeightChart_derivative V e he i hx)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
