import OAI.Analysis.Fourier.Restriction.ConvolutionExpansion

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Pointwise restriction extraction from two nearby radial evaluations of an
oscillatory convolution kernel. -/
theorem twoRadius_fourier_bound {n : ℕ} {K : Space n → ℂ}
    (hKm : Measurable K) {M : ℝ} (hKb : ∀ x, ‖K x‖ ≤ M)
    (β A B C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖(‖x‖ ^ β : ℝ) * K x - (radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (f : Space n → ℂ), Integrable f →
      (∀ y, R < ‖y‖ → f y = 0) → ∀ (ω : Space n) (t : ℝ),
      ‖ω‖ = 1 → 2 ≤ t → 2 * R ≤ t →
      ‖(A : ℂ) - Complex.I * (B : ℂ)‖ * ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω‖ ≤
        t ^ β * ‖sphericalKernelConvolution K f (t • ω)‖ +
        (t + Real.pi / 2) ^ β * ‖sphericalKernelConvolution K f ((t + Real.pi / 2) • ω)‖ +
        D * (1 + R ^ 2) / t * ∫ y, ‖f y‖ := by
  obtain ⟨D, hD, hExp⟩ := farField_kernel_expansion K β A B C hC hK
  refine ⟨2 * D, by positivity, ?_⟩
  intro R hR f hf hfs ω t hω ht hRt
  have ht0 : 0 < t := by linarith
  have herr (s : ℝ) (hs : t ≤ s) :
      ‖(s ^ β : ℝ) * sphericalKernelConvolution K f (s • ω) - radialConvolutionModel A B f ω s‖ ≤
        (D * (1 + R ^ 2) / t) * ∫ y, ‖f y‖ := by
    apply convolution_radialModel_error hKm hKb hf A B s (s ^ β) R
      (D * (1 + R ^ 2) / t) ω (by positivity) hfs
    intro y hy
    have hs0 : 0 < s := ht0.trans_le hs
    have hy' : ‖y‖ ≤ s / 2 := by linarith
    apply (hExp ω y s hω (ht.trans hs) hy').trans
    have hsq : ‖y‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
    calc
      _ ≤ D * (1 + R ^ 2) / s := by gcongr
      _ ≤ D * (1 + R ^ 2) / t := div_le_div_of_nonneg_left (by positivity) ht0 hs
  have hmodel (s : ℝ) (hs : t ≤ s) :
      ‖radialConvolutionModel A B f ω s‖ ≤
        s ^ β * ‖sphericalKernelConvolution K f (s • ω)‖ +
        (D * (1 + R ^ 2) / t) * ∫ y, ‖f y‖ := by
    have H := norm_sub_norm_le (radialConvolutionModel A B f ω s)
      (((s ^ β : ℝ) : ℂ) * sphericalKernelConvolution K f (s • ω))
    rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (ht0.trans_le hs) _)] at H
    linarith [herr s hs]
  have hs : t ≤ t + Real.pi / 2 := by linarith [Real.pi_pos]
  have H := norm_sub_le (radialConvolutionModel A B f ω t)
    (Complex.I * radialConvolutionModel A B f ω (t + Real.pi / 2))
  rw [radialConvolutionModel_outgoing A B t ω hf, norm_mul, norm_mul,
    norm_mul, Complex.norm_I, one_mul] at H
  have hexp : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [hexp, mul_one] at H
  have H1 := hmodel t le_rfl
  have H2 := hmodel (t + Real.pi / 2) hs
  calc
    _ ≤ (t ^ β * ‖sphericalKernelConvolution K f (t • ω)‖ +
          D * (1 + R ^ 2) / t * ∫ y, ‖f y‖) +
        ((t + Real.pi / 2) ^ β * ‖sphericalKernelConvolution K f ((t + Real.pi / 2) • ω)‖ +
          D * (1 + R ^ 2) / t * ∫ y, ‖f y‖) := H.trans (add_le_add H1 H2)
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
