import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NormIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Linear Norm Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LinearNormIntegral

noncomputable section

/-! A bounded real linear map preserves the literal squared-norm integral estimate. -/

open _root_.MeasureTheory

variable {X F G : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem continuousLinearMap_norm_sq_le (L : F →L[ℝ] G) (v : F) :
    ‖L v‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg (L v)) (mul_nonneg (norm_nonneg L) (norm_nonneg v))).mpr (L.le_opNorm v)
  rwa [mul_pow] at h

theorem continuousLinearMap_norm_sq_integral_bound (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (L : F →L[ℝ] G) (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x, ‖L (f x)‖ ^ 2 ∂μ) ≤ ‖L‖ ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi := Compact.NormIntegral.compact_norm_sq_integrable μ f hf hc
  have hL := Compact.NormIntegral.compact_norm_sq_integrable μ (fun x => L (f x)) (L.continuous.comp hf)
    (hc.comp_left (L.map_zero))
  have hb := integral_mono hL (hi.const_mul (‖L‖ ^ 2)) (fun x => continuousLinearMap_norm_sq_le L (f x))
  rwa [integral_const_mul] at hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LinearNormIntegral
