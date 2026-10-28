import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp

/-! # Localization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization

noncomputable section

/-! A bounded coordinate localization of every actual original bundle Hilbert completion. -/

open _root_.TopologicalSpace _root_.MeasureTheory
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

theorem holomorphicLineFrameCoefficientsLp_bound :
    ∃ C : ℝ, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
      ‖CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a‖ ≤
        C * ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a‖ := by
  obtain ⟨c, hc, hcoord⟩ := Analysis.HodgeTheory.Decomposition.Coordinate.Constructions.projective_supported_coordinate_norm_bound V e he n
    (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
  obtain ⟨B, hB, hb⟩ := h.frameCutoff_integral_bound V e i f hf hs
  refine ⟨Real.sqrt (B / c), fun a => ?_⟩
  have ht := hcoord (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a)
    (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_zero V u e i n f hf hs a)
  have hn := CoordinatesLp.holomorphicLineFrameCoefficientsLp_norm_sq V e he i n f hf hs a
  have hh : c * ‖CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a‖ ^ 2 ≤
      B * (h.formIntegralPair V n a a).re :=
    (congrArg (fun r : ℝ => c * r) hn).trans_le (ht.trans (hb n a))
  have hh' := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hc).le
  have heq : c⁻¹ * (c * ‖CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a‖ ^ 2) =
      ‖CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a‖ ^ 2 := by
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hr : c⁻¹ * (B * (h.formIntegralPair V n a a).re) =
      (B / c) * ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a‖ ^ 2 := by
    rw [Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq]
    ring
  exact HolomorphicMetric.Equivalence.nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) (div_pos hB hc).le
    (heq.symm.trans_le (hh'.trans_eq hr))

def holomorphicMetricFrameL2Localization : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n →L[ℂ]
    Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs).extendOfNorm (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n)

theorem holomorphicMetricFrameL2Localization_on_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicMetricFrameL2Localization V h e he i n f hf hs (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a) =
      CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a :=
  LinearMap.extendOfNorm_eq (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n)
    (holomorphicLineFrameCoefficientsLp_bound V h e he i n f hf hs) a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization
