import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.Energy
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OneFieldBound

/-! # Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Ordinary first derivatives of actual compact cutoff chart fields are controlled by the original global Dolbeault energy. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFieldNorm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1),
      Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a) ≤
        C * (h.formIntegralPair V 1 (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)).re := by
  let T := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f
  have hT : IsCompact T := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
  have hTD := HolomorphicCompact.ChartField.holomorphicLineCutoff_image_domain V e i f hs
  obtain ⟨C, hC, hb⟩ := h.projectiveOneField_metric_bound V e he i hT hTD
  refine ⟨C, hC, fun a => ?_⟩
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a
  have hc := Compact.NormIntegral.compact_norm_sq_integrable volume c
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a).continuous
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs a)
  have hS := h.compactFrameSelfPair_integrable V e he i 1 f hf hs a
  have hp (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ‖c z‖ ^ 2 ≤ C * (h.compactFrameSelfPair V e i 1 f hf hs a z).re := by
    by_cases hz : z ∈ tsupport c
    · exact hb z (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport_image V e i 1 f hf hs a hz) (c z)
    · have hz0 : c z = 0 := image_eq_zero_of_notMem_tsupport hz
      change ‖c z‖ ^ 2 ≤ C * (_ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ (c z) (c z)).re
      simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner,
        map_zero, inner_zero_right, mul_zero, Complex.zero_re, le_refl]
  have hi := integral_mono hc (hS.re.const_mul C) hp
  change (∫ z, ‖c z‖ ^ 2) ≤ ∫ z, C * (h.compactFrameSelfPair V e i 1 f hf hs a z).re at hi
  have heS : (∫ z, (h.compactFrameSelfPair V e i 1 f hf hs a z).re) =
      (∫ z, h.compactFrameSelfPair V e i 1 f hf hs a z).re := integral_re hS
  rw [integral_const_mul, heS, h.compactFrameSelfPair_integral V e he i 1 f hf hs a] at hi
  exact hi

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactOrdinaryDerivative_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
      (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), ‖v‖ = 1 →
      let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
      Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) v ≤
        C * (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V A) A.val).re +
          D * (h.formIntegralPair V 1 A.val A.val).re := by
  let T := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f
  have hT : IsCompact T := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
  have hTD := HolomorphicCompact.ChartField.holomorphicLineCutoff_image_domain V e i f hs
  obtain ⟨C, D, hC, hD, hb⟩ := h.projectiveOrdinaryDerivative_integral_bound V e he 1 i hT hTD
  obtain ⟨K, hK, heB⟩ := h.compactFullEnergy_bound V e he i f hf hs
  obtain ⟨M, hM, hnB⟩ := h.compactFieldNorm_bound V e he i f hf hs
  refine ⟨2 * C, C * K + D * M, by positivity, by positivity, fun a v hv => ?_⟩
  have hd := hb (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i 1 f hf hs a.val)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport_image V e i 1 f hf hs a.val) v hv
  have hsum := add_le_add (mul_le_mul_of_nonneg_left (heB a) hC.le)
    (mul_le_mul_of_nonneg_left (hnB a.val) hD.le)
  exact hd.trans (hsum.trans_eq (by dsimp only [HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm]; ring))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactOrdinaryDerivative_dolbeault_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
      (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), ‖v‖ = 1 →
      let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
      Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) v ≤
        C * ((h.formIntegralPair V 0 (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 A.val)).re +
          (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val).re) +
            D * (h.formIntegralPair V 1 A.val A.val).re := by
  obtain ⟨C, D, hC, hD, hb⟩ := h.compactOrdinaryDerivative_bound V e he i f hf hs
  refine ⟨C, D, hC, hD, fun a v hv => ?_⟩
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  have hp := (congrArg Complex.re (h.smoothDolbeaultLaplacianOne_pair V A A)).trans (Complex.add_re _ _)
  exact (hb a v hv).trans_eq (congrArg (fun r : ℝ => C * r + D * (h.formIntegralPair V 1 A.val A.val).re) hp)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
