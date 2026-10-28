import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.BochnerCross
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.PairIntegrability

/-! # Bochner Cross Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Genuine integration by parts for the original full Bochner formula with two independent compact bundle forms. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughCrossPair_integrable (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    Integrable (h.compactFullRoughCrossPair V e i f hf hs a c) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughDivergence.lineCovectorFullRoughCrossPair_integrable volume _ 1 _ _ _ _ _ _ D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hz => hz.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hz => hz.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvatureCrossPair_integrable (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    Integrable (h.compactFullCurvatureCrossPair V e i f hf hs a c) := by
  have heq : h.compactFullCurvatureCrossPair V e i f hf hs a c = fun z =>
      h.compactFramePair V e i 1 f hf hs c.val
        (h.smoothDolbeaultLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)) z -
          (1 / 2 : ℂ) * h.compactFullRoughCrossPair V e i f hf hs a c z := by
    funext z
    have hp := h.compactBochnerCrossPair V e he i f hf hs a c z
    linear_combination -hp
  rw [heq]
  exact (h.compactFramePair_integrable V e he i f hf hs 1 c.val _).sub
    ((h.compactFullRoughCrossPair_integrable V e he i f hf hs a c).const_mul (1 / 2 : ℂ))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactBochnerCross_integral (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
    let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c
    let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
    let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
    h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V A) C.val =
      (1 / 2 : ℂ) * (∫ z, Line.RoughDivergence.lineCovectorFullEnergyPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (h.projectiveWeightChart V e i) s t z) + (∫ z, h.compactFullCurvatureCrossPair V e i f hf hs a c z) := by
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  have hR := h.compactFullRoughCrossPair_integrable V e he i f hf hs a c
  have hC := h.compactFullCurvatureCrossPair_integrable V e he i f hf hs a c
  have hri := h.projectiveFullRoughLaplacian_integral_cross_pair V e he 1 i
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val)
  change (∫ z, h.compactFullRoughCrossPair V e i f hf hs a c z) = _ at hri
  calc
    _ = ∫ z, h.compactFramePair V e i 1 f hf hs c.val (h.smoothDolbeaultLaplacianOne V A) z :=
      (h.compactFramePair_integral V e he i 1 f hf hs c.val _).symm
    _ = ∫ z, ((1 / 2 : ℂ) * h.compactFullRoughCrossPair V e i f hf hs a c z +
        h.compactFullCurvatureCrossPair V e i f hf hs a c z) :=
      integral_congr_ae (Filter.Eventually.of_forall (h.compactBochnerCrossPair V e he i f hf hs a c))
    _ = _ := by
      rw [integral_add (hR.const_mul (1 / 2 : ℂ)) hC, integral_const_mul, hri]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
