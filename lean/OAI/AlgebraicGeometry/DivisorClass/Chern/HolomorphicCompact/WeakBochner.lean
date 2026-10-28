import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.BochnerCrossIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.SupportedPairSymmetry

/-! # Weak Bochner -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original compact Bochner identity in the real weak-equation orientation: the source is paired with the Laplacian of the independent test. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicCompact.WeakBochner.complex_half_add_re (z w : ℂ) :
    ((1 / 2 : ℂ) * z + w).re = (1 / 2 : ℝ) * z.re + w.re := by
  simp only [Complex.add_re, Complex.mul_re]
  norm_num

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactWeakCurvaturePair (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) s
    (fun z => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (t z))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvatureCrossPair_re_swap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    (h.compactFullCurvatureCrossPair V e i f hf hs c a z).re =
      (h.compactWeakCurvaturePair V e i f hf hs a c z).re := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  let R := fun x => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e x)
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) x (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val x) (t x)
  exact Line.SupportedPairSymmetry.lineMetricTestPair_re_symm_of_support b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (h.projectiveWeightChart V e i) R s
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)
    (fun x hx => by rw [h.projectiveWeightChart_apply V e i hx, Complex.ofReal_re]) z

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactWeakBochner_integral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
    let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c
    let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
    let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
    (h.formIntegralPair V 1 A.val (h.smoothDolbeaultLaplacianOne V C)).re =
      (1 / 2 : ℝ) * (∫ z, (Line.RoughDivergence.lineCovectorFullEnergyPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (h.projectiveWeightChart V e i) s t z).re) +
          (∫ z, (h.compactWeakCurvaturePair V e i f hf hs a c z).re) := by
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  let C := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let energy := Line.RoughDivergence.lineCovectorFullEnergyPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i)
  have hsym : (h.formIntegralPair V 1 A.val (h.smoothDolbeaultLaplacianOne V C)).re =
      (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V C) A.val).re := by
    simpa only [Complex.conj_re] using congrArg Complex.re
      (h.formIntegralPair_conj V 1 (h.smoothDolbeaultLaplacianOne V C) A.val)
  have hi := congrArg Complex.re (h.compactBochnerCross_integral V e he i f hf hs c a)
  have hE := h.projectiveFullEnergyPair_integrable V e he 1 i t s
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
  have hEswap : (∫ z, (energy t s z).re) = ∫ z, (energy s t z).re := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (Line.SupportedPairSymmetry.lineCovectorFullEnergyPair_re_symm_of_support b 1 _ _ _ _ t s
      (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val)
      (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
      (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)
      (fun x hx => by rw [h.projectiveWeightChart_apply V e i hx, Complex.ofReal_re]))
  have hCswap : (∫ z, (h.compactFullCurvatureCrossPair V e i f hf hs c a z).re) =
      ∫ z, (h.compactWeakCurvaturePair V e i f hf hs a c z).re :=
    integral_congr_ae (Filter.Eventually.of_forall (h.compactFullCurvatureCrossPair_re_swap V e he i f hf hs a c))
  have heval := (integral_re hE).symm.trans hEswap
  have hceval := (integral_re (h.compactFullCurvatureCrossPair_integrable V e he i f hf hs c a)).symm.trans hCswap
  exact hsym.trans (hi.trans ((HolomorphicCompact.WeakBochner.complex_half_add_re _ _).trans
    (congrArg₂ (fun x y : ℝ => (1 / 2 : ℝ) * x + y) heval hceval)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
