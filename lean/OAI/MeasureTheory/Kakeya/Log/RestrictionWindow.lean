import OAI.Analysis.Fourier.Restriction.TwoRadiusNorm
import OAI.Analysis.Fourier.Restriction.RateAlgebra

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem radialConvolutionModel_mul {n : ℕ} (a A B : ℝ)
    (f : Space n → ℂ) (ω : Space n) (t : ℝ) :
    OAI.Analysis.Fourier.Restriction.radialConvolutionModel (a * A) (a * B) f ω t =
      (a : ℂ) * OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω t := by
  unfold OAI.Analysis.Fourier.Restriction.radialConvolutionModel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [OAI.Analysis.Fourier.Restriction.radialOscillation, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- A slowly varying radial window may multiply the leading oscillation.
The two-radius extraction only needs this window to be bounded below; it
does not need a uniform global asymptotic for the thin-shell kernel. -/
theorem windowed_twoRadius_fourier_bound {n : ℕ} {K f : Space n → ℂ}
    (hKm : Measurable K) {M : ℝ} (hKb : ∀ x, ‖K x‖ ≤ M)
    (hf : Integrable f) {R T β c E : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hc : 0 ≤ c) (hE : 0 ≤ E) (A B : ℝ) (w : ℝ → ℝ)
    (hfs : ∀ y, R < ‖y‖ → f y = 0)
    (hw : ∀ t ∈ Icc T (3 * T), c ≤ w t)
    (herror : ∀ (ω : Space n), ‖ω‖ = 1 → ∀ t ∈ Icc T (3 * T),
      ∀ y, ‖y‖ ≤ R →
      ‖((T * t ^ β : ℝ) : ℂ) * K (t • ω - y) -
        (w t : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤ E)
    (ω : Space n) (hω : ‖ω‖ = 1) (t : ℝ) (ht : t ∈ Icc T (2 * T))
    (hpi : Real.pi / 2 ≤ T) :
    (c * ‖(A : ℂ) - Complex.I * (B : ℂ)‖) * ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω‖ ≤
      (3 * T) ^ (β + 1) * (‖OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f (t • ω)‖ +
        ‖OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f ((t + Real.pi / 2) • ω)‖) +
      (2 * E) * ∫ y, ‖f y‖ := by
  have herr (s : ℝ) (hs : s ∈ Icc T (3 * T)) :
      ‖((T * s ^ β : ℝ) : ℂ) * OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f (s • ω) -
        (w s : ℂ) * OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω s‖ ≤ E * ∫ y, ‖f y‖ := by
    rw [← radialConvolutionModel_mul]
    apply OAI.Analysis.Fourier.Restriction.convolution_radialModel_error hKm hKb hf (w s * A) (w s * B) s
      (T * s ^ β) R E ω hE hfs
    intro y hy
    convert herror ω hω s hs y hy using 1
    simp only [OAI.Analysis.Fourier.Restriction.radialOscillation, Complex.ofReal_add, Complex.ofReal_mul]
    ring_nf
  have hmodel (s : ℝ) (hs : s ∈ Icc T (3 * T)) :
      c * ‖OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω s‖ ≤
        (3 * T) ^ (β + 1) * ‖OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f (s • ω)‖ +
        E * ∫ y, ‖f y‖ := by
    have hs0 : 0 < s := hT.trans_le hs.1
    have hw0 : 0 ≤ w s := hc.trans (hw s hs)
    have H := norm_sub_norm_le ((w s : ℂ) * OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω s)
      (((T * s ^ β : ℝ) : ℂ) * OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f (s • ω))
    rw [norm_sub_rev, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0,
      abs_of_nonneg (mul_nonneg hT.le (Real.rpow_nonneg hs0.le _))] at H
    have hpow : T * s ^ β ≤ (3 * T) ^ (β + 1) := by
      rw [Real.rpow_add_one (by positivity : 3 * T ≠ 0)]
      calc
        T * s ^ β ≤ T * (3 * T) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs0.le hs.2 hβ) hT.le
        _ ≤ (3 * T) ^ β * (3 * T) := by nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 3 * T) β]
    have hlow := mul_le_mul_of_nonneg_right (hw s hs) (norm_nonneg (OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω s))
    have hupp := mul_le_mul_of_nonneg_right hpow (norm_nonneg (OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f (s • ω)))
    linarith [herr s hs]
  have ht' : t ∈ Icc T (3 * T) := ⟨ht.1, by linarith [ht.2]⟩
  have hs' : t + Real.pi / 2 ∈ Icc T (3 * T) := by
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have H := norm_sub_le (OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω t)
    (Complex.I * OAI.Analysis.Fourier.Restriction.radialConvolutionModel A B f ω (t + Real.pi / 2))
  rw [OAI.Analysis.Fourier.Restriction.radialConvolutionModel_outgoing A B t ω hf, norm_mul, norm_mul,
    norm_mul, Complex.norm_I, one_mul] at H
  have hexp : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [hexp, mul_one] at H
  have Hc := mul_le_mul_of_nonneg_left H hc
  have H1 := hmodel t ht'
  have H2 := hmodel (t + Real.pi / 2) hs'
  nlinarith

/-- Integrating the windowed extraction cancels the radial Jacobian. The
thin shell contributes one extra power of the observation radius. -/
theorem windowed_twoRadius_fourier_norm_bound {n : ℕ} (hn : 1 ≤ n)
    {K f : Space n → ℂ} (hKm : Measurable K) {M : ℝ} (hKb : ∀ x, ‖K x‖ ≤ M)
    (hfm : Measurable f) (hf : Integrable f) {R T β c E p : ℝ}
    (hT : 0 < T) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hE : 0 ≤ E) (hp : 1 ≤ p)
    (A B : ℝ) (w : ℝ → ℝ) (hfs : ∀ y, R < ‖y‖ → f y = 0)
    (hw : ∀ t ∈ Icc T (3 * T), c ≤ w t)
    (herror : ∀ (ω : Space n), ‖ω‖ = 1 → ∀ t ∈ Icc T (3 * T),
      ∀ y, ‖y‖ ≤ R →
      ‖((T * t ^ β : ℝ) : ℂ) * K (t • ω - y) -
        (w t : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤ E)
    (hpi : Real.pi / 2 ≤ T) :
    ENNReal.ofReal (c * ‖(A : ℂ) - Complex.I * (B : ℂ)‖) *
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (2 * 3 ^ (β + 1) * T ^ (β + 1 - (n : ℝ) / p)) *
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution K f) (ENNReal.ofReal p) volume +
      ENNReal.ofReal ((2 * E) * ∫ y, ‖f y‖) * OAI.Analysis.Fourier.Restriction.sphereMeasure n univ ^ (1 / p) := by
  apply OAI.Analysis.Fourier.Restriction.annular_inequality_normalize hn hT (by linarith) (β + 1)
  have H := OAI.Analysis.Fourier.Restriction.annular_norm_pair_bound hn (OAI.Analysis.Fourier.Restriction.continuous_angularFourier hf).measurable
    (OAI.Analysis.Fourier.Restriction.measurable_sphericalKernelConvolution hKm hfm) hp
    (mul_nonneg hc (norm_nonneg _)) (by positivity : 0 ≤ (3 * T) ^ (β + 1))
    (by positivity : 0 ≤ (2 * E) * ∫ y, ‖f y‖) hT (by positivity : 0 ≤ Real.pi / 2)
    (b := 2 * T) (windowed_twoRadius_fourier_bound hKm hKb hf hT hβ hc hE A B w hfs hw herror · · · · hpi)
  simpa only [show 2 * T - T = T by ring] using H

end OAI.MeasureTheory.Kakeya
