import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization

/-! # Multiplier -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Multiplier

noncomputable section

/-! Original smooth scalar multiplication extends to a genuine bounded operator on every actual bundle Hilbert completion. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (n : ℕ) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)

def holomorphicMetricSmoothL2Multiplier : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] IntegralPairZero.HolomorphicFormL2With V h n :=
  (IntegralPairZero.holomorphicFormL2WithInclusion V h n).comp (SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf)

theorem holomorphicMetricSmoothL2Multiplier_bound :
    ∃ C : ℝ, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
      ‖holomorphicMetricSmoothL2Multiplier V h n f hf a‖ ≤ C * ‖IntegralPairZero.holomorphicFormL2WithInclusion V h n a‖ := by
  obtain ⟨C, hC, hb⟩ := h.smoothMul_integral_bound V f hf
  refine ⟨Real.sqrt C, fun a => ?_⟩
  apply HolomorphicMetric.Equivalence.nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) hC.le
  change ‖IntegralPairZero.holomorphicFormL2WithInclusion V h n (SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a)‖ ^ 2 ≤ _
  rw [IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq, IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq]
  exact hb n a

def holomorphicMetricL2Multiplier : IntegralPairZero.HolomorphicFormL2With V h n →L[ℂ] IntegralPairZero.HolomorphicFormL2With V h n :=
  (holomorphicMetricSmoothL2Multiplier V h n f hf).extendOfNorm (IntegralPairZero.holomorphicFormL2WithInclusion V h n)

theorem holomorphicMetricL2Multiplier_on_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicMetricL2Multiplier V h n f hf (IntegralPairZero.holomorphicFormL2WithInclusion V h n a) =
      IntegralPairZero.holomorphicFormL2WithInclusion V h n (SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) :=
  LinearMap.extendOfNorm_eq (IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n)
    (holomorphicMetricSmoothL2Multiplier_bound V h n f hf) a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Multiplier
