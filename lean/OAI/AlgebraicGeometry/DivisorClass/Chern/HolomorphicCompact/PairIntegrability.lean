import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.Bochner
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.Energy

/-! # Pair Integrability -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Integrability of the actual compact cutoff Bochner pairings. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair_integrable (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Integrable (h.compactFramePair V e i n f hf hs a b) := by
  let U := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e U
  exact Line.TensorMetricTest.lineMetricTestPair_integrable volume _ n _ _ _ _ D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hz => hz.1))
    (h.projectiveWeightChart_smooth V e he i)
    ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he (⊤ ⊓ U) n (b.val i)).mono
      (fun _ hz => ⟨hz.1, trivial, hz.2⟩))
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i n f hf hs a)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i n f hf hs a)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i n f hf hs a)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughPair_integrable
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    Integrable (h.compactFullRoughPair V e i f hf hs a) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact Line.RoughDivergence.lineCovectorFullRoughPair_integrable volume _ 1 _ _ _ _ _ D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hz => hz.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hz => hz.1))
    (h.projectiveConnectionChart_smooth V e he i) (h.projectiveWeightChart_smooth V e he i)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (fun _ hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair_integrable
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    Integrable (h.compactFullCurvaturePair V e i f hf hs a) := by
  have heq : h.compactFullCurvaturePair V e i f hf hs a = fun z =>
      h.compactFramePair V e i 1 f hf hs a.val
        (h.smoothDolbeaultLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)) z -
          (1 / 2 : ℂ) * h.compactFullRoughPair V e i f hf hs a z := by
    funext z
    have hp := h.compactBochnerPair V e he i f hf hs a z
    linear_combination -hp
  rw [heq]
  exact (h.compactFramePair_integrable V e he i f hf hs 1 a.val _).sub
    ((h.compactFullRoughPair_integrable V e he i f hf hs a).const_mul (1 / 2 : ℂ))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
