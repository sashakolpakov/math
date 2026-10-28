import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Rescale Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact original pointwise and integral metric pairings after an actual smooth positive scalar rescaling. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ f) (hp : ∀ x, 0 < f x)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.rescale_ratio (x : V.analyticSpace) :
    (h.rescale f hf hp).ratio h x = f x := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.ratio_onOpen _ h x
    ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x⟩]
  change (f x * h.weight x ⟨x, _⟩) / h.weight x ⟨x, _⟩ = f x
  exact mul_div_cancel_right₀ (f x) (ne_of_gt (h.positive x _))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.rescale_globalFormPair (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    (h.rescale f hf hp).globalFormPair V n a b x = (f x : ℂ) * h.globalFormPair V n a b x :=
  ((h.rescale f hf hp).globalFormPair_change V n h a b x).trans
    (congrArg (fun r : ℝ => (r : ℂ) * h.globalFormPair V n a b x) (h.rescale_ratio V f hf hp x))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.rescale_globalFormPair_re (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    ((h.rescale f hf hp).globalFormPair V n a b x).re = f x * (h.globalFormPair V n a b x).re := by
  rw [h.rescale_globalFormPair V f hf hp n a b x]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.rescale_formIntegralPair_re (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ((h.rescale f hf hp).formIntegralPair V n a b).re =
      ∫ x, f x * (h.globalFormPair V n a b x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  ((h.rescale f hf hp).formIntegralPair_re V n a b).trans
    (integral_congr_ae (Filter.Eventually.of_forall (h.rescale_globalFormPair_re V f hf hp n a b)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
