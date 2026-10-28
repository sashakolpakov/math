import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint

/-! # Norm Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Compact original frame cutoffs are bounded by the actual bundle metric. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include hf in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameCutoff_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : V.analyticSpace) (hx : x ∈ tsupport f),
      ‖f x‖ ^ 2 ≤ C * h.weight i ⟨x, (hs hx).2⟩ := by
  let K := tsupport f
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isClosed_tsupport f).isCompact
  let j : K → Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i :=
    fun x => ⟨x.val, (hs x.property).2⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hw : Continuous (fun x : K => h.weight i (j x)) := (h.smooth i).continuous.comp hj
  have hr : Continuous (fun x : K => ‖f x.val‖ ^ 2 / h.weight i (j x)) :=
    ((hf.continuous.comp continuous_subtype_val).norm.pow 2).div hw
      (fun x => (h.positive i (j x)).ne')
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hr.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  have hb := (hB (Set.mem_image_of_mem _ (Set.mem_univ (⟨x, hx⟩ : K)))).trans (le_max_left B 1)
  exact (div_le_iff₀ (h.positive i ⟨x, (hs hx).2⟩)).mp hb

theorem HolomorphicFrame.NormBound.holomorphicLineChartFrameTest_self_pair (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) (hx : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a).val
      (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a).val x).re =
      ‖f x‖ ^ 2 * (Projective.CovectorPair.projectiveTangentCovectorPair V n x
        (a.val i ⟨x, trivial, hx⟩) (a.val i ⟨x, trivial, hx⟩)).re := by
  rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
    Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_apply V u e i n f hf hs a ⟨x, hx⟩,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, Projective.CovectorPair.projectiveTangentCovectorPair_smul_right,
    ← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameCutoff_point_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) x,
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a).val
        (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a).val x).re ≤
          C * (h.globalFormPair V n a a x).re := by
  obtain ⟨C, hC, hb⟩ := h.frameCutoff_ratio_bound V e i f hf hs
  refine ⟨C, hC, fun n a x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · rw [HolomorphicFrame.NormBound.holomorphicLineChartFrameTest_self_pair V e i f hf hs n a x (hs hx).2,
      h.globalFormPair_inFrame V n a a i x (hs hx).2,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb x hx) (Projective.CovectorPair.projectiveTangentCovectorPair_nonneg V n x _)
  · rw [Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n _ _ x
      (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_zero V u e i n f hf hs a x hx)]
    exact mul_nonneg hC.le (h.globalFormPair_nonneg V n a x)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameCutoff_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n),
      (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a)
        (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a)).re ≤
          C * (h.formIntegralPair V n a a).re := by
  obtain ⟨C, hC, hb⟩ := h.frameCutoff_point_bound V e i f hf hs
  refine ⟨C, hC, fun n a => ?_⟩
  let b := Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a
  have hi : Integrable (fun x => Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b.val b.val x) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
    rw [← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
    exact Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V n b b
  calc
    _ = (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b.val b.val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).re :=
      congrArg Complex.re (Projective.MetricAdjoint.projectiveL2Pair_actualMetricIntegral V n b b)
    _ = ∫ x, (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b.val b.val x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      (integral_re hi).symm
    _ ≤ ∫ x, C * (h.globalFormPair V n a a x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_mono hi.re ((h.globalFormPair_integrable V n a a).re.const_mul C) (hb n a)
    _ = _ := (integral_const_mul C _).trans (congrArg (fun r : ℝ => C * r) (h.formIntegralPair_re V n a a).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
