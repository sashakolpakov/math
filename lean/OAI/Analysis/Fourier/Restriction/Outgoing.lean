import OAI.Analysis.Fourier.Restriction.RadialModel

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Two radii a quarter period apart isolate the outgoing exponential. -/
theorem radialOscillation_outgoing (A B θ : ℝ) :
    (radialOscillation A B θ : ℂ) - Complex.I *
      (radialOscillation A B (θ + Real.pi / 2) : ℝ) =
    ((A : ℂ) - Complex.I * (B : ℂ)) * Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I]
  simp only [radialOscillation, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_cos, Complex.ofReal_sin]
  ring_nf
  simp [Complex.I_sq]

theorem outgoing_coefficient_ne_zero {A B : ℝ} (h : 0 < A ^ 2 + B ^ 2) :
    (A : ℂ) - Complex.I * (B : ℂ) ≠ 0 := by
  intro H
  have hr := congrArg Complex.re H
  have hi := congrArg Complex.im H
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, zero_mul, Complex.I_im, sub_self, sub_zero, Complex.zero_re] at hr
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, one_mul, mul_zero, zero_add, zero_sub, Complex.zero_im, neg_eq_zero] at hi
  nlinarith

end OAI.Analysis.Fourier.Restriction
