import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.CurvatureBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovariantIntegralBound

/-! # Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Full covariant energy of actual cutoff forms is controlled by their original global Dolbeault energy. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactBochner_integral (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
    let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
    h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V A) A.val =
      (1 / 2 : ℂ) * (∫ z, Line.RoughDivergence.lineCovectorFullEnergy (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (h.projectiveWeightChart V e i) c z) + (∫ z, h.compactFullCurvaturePair V e i f hf hs a z) := by
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  have hR := h.compactFullRoughPair_integrable V e he i f hf hs a
  have hC := h.compactFullCurvaturePair_integrable V e he i f hf hs a
  have hri := h.projectiveFullRoughLaplacian_integral_pair V e he 1 i
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
  change (∫ z, h.compactFullRoughPair V e i f hf hs a z) = _ at hri
  calc
    _ = ∫ z, h.compactFramePair V e i 1 f hf hs a.val (h.smoothDolbeaultLaplacianOne V A) z :=
      (h.compactFramePair_integral V e he i 1 f hf hs a.val _).symm
    _ = ∫ z, ((1 / 2 : ℂ) * h.compactFullRoughPair V e i f hf hs a z + h.compactFullCurvaturePair V e i f hf hs a z) :=
      integral_congr_ae (Filter.Eventually.of_forall (h.compactBochnerPair V e he i f hf hs a))
    _ = _ := by
      rw [integral_add (hR.const_mul (1 / 2 : ℂ)) hC, integral_const_mul, hri]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactBochner_integral_re (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
    (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V A) A.val).re =
      (1 / 2 : ℝ) * h.projectiveFullEnergyIntegral V e 1 i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) +
        (∫ z, h.compactFullCurvaturePair V e i f hf hs a z).re := by
  have hi := congrArg Complex.re (h.compactBochner_integral V e he i f hf hs a)
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num] at hi
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hi
  exact hi

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullEnergy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
      h.projectiveFullEnergyIntegral V e 1 i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) ≤
        2 * (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V A) A.val).re +
          C * (h.formIntegralPair V 1 A.val A.val).re := by
  obtain ⟨C, hC, hb⟩ := h.compactFullCurvaturePair_integral_lower V e he i f hf hs
  refine ⟨2 * C, by positivity, fun a => ?_⟩
  have hi := h.compactBochner_integral_re V e he i f hf hs a
  have hc := hb a
  dsimp only at hi ⊢
  linarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
