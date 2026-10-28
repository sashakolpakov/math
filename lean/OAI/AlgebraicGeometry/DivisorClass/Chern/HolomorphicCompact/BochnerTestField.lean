import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.WeakBochner
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalProjectedBochnerPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Bochner Test Field -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original compact weak Bochner integral is a single unprojected test density, with the required projection retained in the curvature action. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactWeakBochner_test_field (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (p : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1)
    (hp : Differentiable ℝ p)
    (ht : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection (p z)) :
    (h.formIntegralPair V 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val
      (h.smoothDolbeaultLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c))).re =
      ∫ z, h.projectiveBochnerWeakPair V e i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) p z := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  let energy := Line.RoughDivergence.lineCovectorFullEnergyPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) s
  let R := fun z v => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) v
  let pair := Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) s
  have hE := h.projectiveFullEnergyPair_integrable V e he 1 i s t
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val)
  have hC : Integrable (fun z => (h.compactWeakCurvaturePair V e i f hf hs a c z).re) :=
    (h.compactFullCurvatureCrossPair_integrable V e he i f hf hs c a).re.congr
      (Filter.Eventually.of_forall (h.compactFullCurvatureCrossPair_re_swap V e he i f hf hs a c))
  have hmerge : (1 / 2 : ℝ) * (∫ z, (energy t z).re) +
      (∫ z, (h.compactWeakCurvaturePair V e i f hf hs a c z).re) =
      ∫ z, (1 / 2 : ℝ) * (energy t z).re + (h.compactWeakCurvaturePair V e i f hf hs a c z).re := by
    have hEr : Integrable (fun z => (energy t z).re) := hE.re
    exact ((integral_add (hEr.const_mul (1 / 2 : ℝ)) hC).trans
      (congrArg (fun r : ℝ => r + ∫ z, (h.compactWeakCurvaturePair V e i f hf hs a c z).re)
        (integral_const_mul (1 / 2 : ℝ) (fun z => (energy t z).re)))).symm
  have hpoint (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      (1 / 2 : ℝ) * (energy t z).re + (h.compactWeakCurvaturePair V e i f hf hs a c z).re =
      h.projectiveBochnerWeakPair V e i s p z := by
    have heq := congrArg (fun T : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 =>
      (1 / 2 : ℝ) * (energy T z).re + (pair (fun y => R y (T y)) z).re) ht
    have hconst := (Line.TensorMetricTest.lineMetricTestPair_constant_values b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      (h.projectiveWeightChart V e i) s (fun y => R y (OneCovectorAntiProjection.oneCovectorAntiProjection (p y))) z).symm
    have hprojected := heq.trans (congrArg (fun r : ℂ =>
      (1 / 2 : ℝ) * (energy (fun y => OneCovectorAntiProjection.oneCovectorAntiProjection (p y)) z).re + r.re) hconst)
    exact hprojected.trans (h.compactProjectedBochnerWeakPair_eq_global V e he i f hf hs a p z (hp z))
  exact (h.compactWeakBochner_integral V e he i f hf hs a c).trans
    (hmerge.trans (integral_congr_ae (Filter.Eventually.of_forall hpoint)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
