import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughCrossIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorIntegration

/-! # Cross Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Integration by parts for two independent fields with the original projective metric and line connection. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullEnergyPair_integrable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : ContDiff ℝ ∞ c) (hcc : HasCompactSupport c)
    (hcs : tsupport c ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Integrable (Line.RoughDivergence.lineCovectorFullEnergyPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (h.projectiveWeightChart V e i) a c) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughDivergence.lineCovectorFullEnergyPair_integrable volume _ n _ _ _ _ a c D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i) ha hs hc hcc hcs
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullRoughLaplacian_integral_cross_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : ContDiff ℝ ∞ c) (hcc : HasCompactSupport c)
    (hcs : tsupport c ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let w := h.projectiveWeightChart V e i
    (∫ x, Line.TensorMetricTest.lineMetricTestPair b n B w (Line.RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) c x) =
      ∫ x, Line.RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughCrossIntegral.lineCovectorFullRoughLaplacian_integral_cross_pair volume _ n _ _ _ _ a c D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i) ha hs hc hcc hcs
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hx.1)
    (fun _ hx => h.projectiveWeightChart_derivative V e he i hx)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
