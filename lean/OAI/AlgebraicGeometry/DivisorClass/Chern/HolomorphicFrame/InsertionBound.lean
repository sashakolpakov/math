import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.NormBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs

/-! # Insertion Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original compact frame insertion is bounded from the base metric integral to the actual bundle metric integral. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))

include hf in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameInsertion_weight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : V.analyticSpace) (hx : x ∈ tsupport f),
      h.weight i ⟨x, hs hx⟩ * ‖f x‖ ^ 2 ≤ C := by
  let K := tsupport f
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isClosed_tsupport f).isCompact
  let j : K → Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i :=
    fun x => ⟨x.val, hs x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hw : Continuous (fun x : K => h.weight i (j x)) := (h.smooth i).continuous.comp hj
  have hr : Continuous (fun x : K => h.weight i (j x) * ‖f x.val‖ ^ 2) :=
    hw.mul ((hf.continuous.comp continuous_subtype_val).norm.pow 2)
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hr.continuousOn
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx =>
    (hB (Set.mem_image_of_mem _ (Set.mem_univ (⟨x, hx⟩ : K)))).trans (le_max_left B 1)⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameInsertion_self_pair (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) (hx : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    (h.globalFormPair V n (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a)
      (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a) x).re =
      (h.weight i ⟨x, hx⟩ * ‖f x‖ ^ 2) * (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re := by
  rw [h.globalFormPair_inFrame V n _ _ i x hx,
    HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_in_frame u i n f hf hs a,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, Projective.CovectorPair.projectiveTangentCovectorPair_smul_right]
  rw [← mul_assoc (conj (f x)) (f x), ← Complex.normSq_eq_conj_mul_self]
  rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq, mul_assoc]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameInsertion_point_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) x,
      (h.globalFormPair V n (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a)
        (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a) x).re ≤
          C * (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re := by
  obtain ⟨C, hC, hb⟩ := h.frameInsertion_weight_bound V i f hf hs
  refine ⟨C, hC, fun n a x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · rw [h.frameInsertion_self_pair V i f hf hs n a x (hs hx)]
    exact mul_le_mul_of_nonneg_right (hb x hx) (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x)
  · have hi := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
    rw [h.globalFormPair_inFrame V n _ _ x x hi,
      HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_zero u i n f hf hs a x ⟨x, trivial, hi⟩ hx,
      Holomorphic.AdjointPointPairs.projectiveTangentCovectorPair_zero_left, mul_zero, Complex.zero_re]
    exact mul_nonneg hC.le (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameInsertion_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n),
      (h.formIntegralPair V n (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a)
        (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a)).re ≤ C * (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n a a).re := by
  obtain ⟨C, hC, hb⟩ := h.frameInsertion_point_bound V i f hf hs
  refine ⟨C, hC, fun n a => ?_⟩
  let b := HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a
  have hi : Integrable (fun x => Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
    rw [← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
    exact Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V n a a
  calc
    _ = ∫ x, (h.globalFormPair V n b b x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := h.formIntegralPair_re V n b b
    _ ≤ ∫ x, C * (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_mono (h.globalFormPair_integrable V n b b).re (hi.re.const_mul C) (hb n a)
    _ = _ := (integral_const_mul C _).trans (congrArg (fun r : ℝ => C * r)
      ((integral_re hi).trans (congrArg Complex.re (Projective.MetricAdjoint.projectiveL2Pair_actualMetricIntegral V n a a).symm)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
