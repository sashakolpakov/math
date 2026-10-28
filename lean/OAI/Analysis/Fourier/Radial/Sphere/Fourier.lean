import OAI.Analysis.Fourier.Radial.Sphere.Kernel

open OAI.Analysis.Fourier.Wave

/-! The surface-measure Fourier integral is real, by antipodal symmetry. -/

open _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem integral_sphere_sine_eq_zero {n : ℕ} (x : Space n) :
    (∫ ω, Real.sin (inner ℝ x ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) = 0 := by
  let e : Space n ≃ₗᵢ[ℝ] Space n := LinearIsometryEquiv.neg ℝ
  have H := (measurePreserving_sphere_orthogonal e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun ω => Real.sin (inner ℝ x ω))
  have He (ω : Space n) : e ω = -ω := rfl
  simp only [He, inner_neg_right, Real.sin_neg, integral_neg] at H
  linarith

theorem sphericalExtension_one_eq_cosine {n : ℕ} (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1 : ℂ)) x =
      (sphereCosineKernel x : ℂ) := by
  have hi : Integrable (fun ω : Space n => Complex.exp (Complex.I *
      (inner ℝ x ω : ℂ))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1 : ℝ)).mono'
      (by fun_prop)
    filter_upwards [] with ω
    simp [Complex.norm_exp]
  simp only [OAI.Analysis.Fourier.Restriction.sphericalExtension, mul_one]
  apply Complex.ext
  · change RCLike.re (∫ ω : Space n, Complex.exp (Complex.I *
        (inner ℝ x ω : ℂ)) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) = sphereCosineKernel x
    rw [← integral_re hi]
    change (∫ ω : Space n, (Complex.exp (Complex.I *
        (inner ℝ x ω : ℂ))).re ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) = sphereCosineKernel x
    simp only [Complex.exp_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, Real.exp_zero,
      Complex.mul_im, zero_add, sphereCosineKernel]
  · change RCLike.im (∫ ω : Space n, Complex.exp (Complex.I *
        (inner ℝ x ω : ℂ)) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) = 0
    rw [← integral_im hi]
    change (∫ ω : Space n, (Complex.exp (Complex.I *
        (inner ℝ x ω : ℂ))).im ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) = 0
    simpa [Complex.exp_im] using integral_sphere_sine_eq_zero x

theorem abs_sphereCosineKernel_le_mass {n : ℕ} (x : Space n) :
    |sphereCosineKernel x| ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ := by
  have H := OAI.Analysis.Fourier.Restriction.norm_sphericalExtension_le (fun _ : Space n => (1 : ℂ)) x
  rw [sphericalExtension_one_eq_cosine] at H
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_one, integral_const,
    smul_eq_mul, mul_one] using H

end OAI.Analysis.Fourier.Radial
