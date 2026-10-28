import OAI.Analysis.Fourier.SquareFunction.Radius.Normalization
import OAI.Analysis.Fourier.SquareFunction.Radius.Continuity

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.Fourier.SquareFunction

/-- The derivative in the defining radius of the actual Bochner--Riesz
Fourier integral. This includes the integrable singularity at the moving
frequency sphere when the exponent is less than one. -/
theorem hasDerivAt_bochnerRiesz_radius {n : ℕ} [NeZero n] {α r : ℝ}
    (hα : 1 / 2 < α) (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    HasDerivAt (fun s => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz α s f x) (r⁻¹ • OAI.Analysis.Fourier.SquareFunction.radiusDerivative α r f x) r := by
  let g : Space n → ℂ := bochnerRieszFrequencyIntegrand f x
  have hg : Integrable g := integrable_bochnerRieszFrequencyIntegrand f x
  have hgc : Continuous g := continuous_bochnerRieszFrequencyIntegrand f x
  have hb : ∀ ξ, ‖g ξ‖ ≤ ∫ y, ‖f y‖ := by
    intro ξ
    rw [show g ξ = bochnerRieszFrequencyIntegrand f x ξ from rfl,
      norm_bochnerRieszFrequencyIntegrand]
    exact OAI.Analysis.Fourier.Restriction.norm_angularFourier_le_integral_norm f ξ
  have hc : ContinuousOn (OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegralDerivative α g) (Ioi 0) := by
    simpa only [OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegralDerivative, OAI.Analysis.Fourier.SquareFunction.radiusPowerDerivative] using!
      OAI.Analysis.Fourier.SquareFunction.continuousOn_radius_derivative_integral hα hgc hb
  have hd := OAI.Analysis.Fourier.SquareFunction.hasDerivAt_radiusPowerIntegral_of_continuousDerivative
    (show 0 < α by linarith) hr hg hc
  rw [radiusDerivative_eq_radiusPowerIntegralDerivative]
  convert hd.const_smul ((((2 * Real.pi)^n)⁻¹ : ℝ)) using 1
  funext s
  exact bochnerRiesz_eq_radiusPowerIntegral α s f x

/-- The multiplier used in the square function is literally `r ∂ᵣ Bᵅᵣ`. -/
theorem radius_smul_deriv_bochnerRiesz {n : ℕ} [NeZero n] {α r : ℝ}
    (hα : 1 / 2 < α) (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    r • deriv (fun s => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz α s f x) r = OAI.Analysis.Fourier.SquareFunction.radiusDerivative α r f x := by
  rw [(hasDerivAt_bochnerRiesz_radius hα hr f x).deriv, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul]

end OAI.Analysis.Fourier.SquareFunction
