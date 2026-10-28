import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.WeakMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiTestEnergy

/-! # Projected Bochner Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual antiholomorphic test projection leaves the compact source's real energy pairing unchanged, while remaining in the full curvature term. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveProjectedBochnerWeakPair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℝ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  (1 / 2 : ℝ) * (Line.RoughDivergence.lineCovectorFullEnergyPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) a (fun y => OneCovectorAntiProjection.oneCovectorAntiProjection (c y)) z).re +
      (Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) (fun _ => a z)
        (fun _ => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (OneCovectorAntiProjection.oneCovectorAntiProjection (c z))) z).re

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactProjectedBochnerWeakPair_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hc : DifferentiableAt ℝ c z)
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveProjectedBochnerWeakPair V e i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) c z =
      h.projectiveBochnerWeakPair V e i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) c z := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  have hp := h.compactFullEnergy_anti_test_re V e he i f hf hs a c hc hz
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r +
    (Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) (fun _ => s z)
      (fun _ => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (OneCovectorAntiProjection.oneCovectorAntiProjection (c z))) z).re) hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
