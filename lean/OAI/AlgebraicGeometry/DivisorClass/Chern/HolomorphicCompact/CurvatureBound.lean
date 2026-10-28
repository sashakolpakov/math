import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.PairIntegrability

/-! # Curvature Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The compact chart norm pairing is exactly the original global norm of the cutoff form. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a
  Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) c c

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair_eq (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.compactFrameSelfPair V e i n f hf hs a =
      h.compactFramePair V e i n f hf hs a (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) := by
  funext z
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · unfold HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair Line.TensorMetricTest.lineMetricTestPair
    rw [HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i n f hf hs a hz]
  · have hc : c z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i n f hf hs a ht))
    change _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ n _ (c z) (c z) = _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ n _ _ (c z)
    simp only [hc, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right]

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair_integrable (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Integrable (h.compactFrameSelfPair V e i n f hf hs a) := by
  rw [h.compactFrameSelfPair_eq V e i n f hf hs a]
  exact h.compactFramePair_integrable V e he i f hf hs n a _

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair_integral (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (∫ z, h.compactFrameSelfPair V e i n f hf hs a z) =
      h.formIntegralPair V n (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) := by
  rw [h.compactFrameSelfPair_eq V e i n f hf hs a]
  exact h.compactFramePair_integral V e he i n f hf hs a _

end

/-! A uniform metric bound for the exact curvature pairing of every original cutoff form. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V),
      |(h.compactFullCurvaturePair V e i f hf hs a z).re| ≤
        C * (h.compactFrameSelfPair V e i 1 f hf hs a.val z).re := by
  let T := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f
  have hT : IsCompact T := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
  have hTD := HolomorphicCompact.ChartField.holomorphicLineCutoff_image_domain V e i f hs
  obtain ⟨C, hC, hb⟩ := h.projectiveFullBochnerCurvature_pair_bound V e he hT (fun _ hz => (hTD hz).1)
  refine ⟨C, hC, fun a z => ?_⟩
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  by_cases hz : z ∈ tsupport c
  · have ht : z ∈ T := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport_image V e i 1 f hf hs a.val hz
    have hd := hTD ht
    have hp := hb z ht (c z)
    have hq : 0 ≤ ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * h.weight i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hd.2⟩ :=
      mul_nonneg (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hd.1).le (h.positive i _).le
    have hmul := mul_le_mul_of_nonneg_left hp hq
    unfold HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFrameSelfPair Line.TensorMetricTest.lineMetricTestPair
    dsimp only
    rw [h.projectiveWeightChart_apply V e i hd]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero]
    change |(ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * h.weight i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hd.2⟩) * _| ≤ _
    rw [abs_mul, abs_of_nonneg hq]
    exact hmul.trans_eq (mul_left_comm _ _ _)
  · have hc : c z = 0 := image_eq_zero_of_notMem_tsupport hz
    change |(_ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (c z)).re| ≤
      C * (_ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ (c z) (c z)).re
    simp only [hc, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, mul_zero,
      Complex.zero_re, abs_zero, le_refl]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair_integral_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      -(C * (h.formIntegralPair V 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val
        (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val).re) ≤
          (∫ z, h.compactFullCurvaturePair V e i f hf hs a z).re := by
  obtain ⟨C, hC, hb⟩ := h.compactFullCurvaturePair_bound V e he i f hf hs
  refine ⟨C, hC, fun a => ?_⟩
  have hS := h.compactFrameSelfPair_integrable V e he i 1 f hf hs a.val
  have hR := h.compactFullCurvaturePair_integrable V e he i f hf hs a
  have hp (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      -(C * (h.compactFrameSelfPair V e i 1 f hf hs a.val z).re) ≤
        (h.compactFullCurvaturePair V e i f hf hs a z).re := (abs_le.mp (hb a z)).1
  have hi := integral_mono (hS.re.const_mul C).neg hR.re hp
  change (∫ z, -(C * (h.compactFrameSelfPair V e i 1 f hf hs a.val z).re)) ≤
    ∫ z, (h.compactFullCurvaturePair V e i f hf hs a z).re at hi
  have heS : (∫ z, (h.compactFrameSelfPair V e i 1 f hf hs a.val z).re) =
      (∫ z, h.compactFrameSelfPair V e i 1 f hf hs a.val z).re := integral_re hS
  have heR : (∫ z, (h.compactFullCurvaturePair V e i f hf hs a z).re) =
      (∫ z, h.compactFullCurvaturePair V e i f hf hs a z).re := integral_re hR
  rw [integral_neg, integral_const_mul, heS, heR,
    h.compactFrameSelfPair_integral V e he i 1 f hf hs a.val] at hi
  exact hi

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
