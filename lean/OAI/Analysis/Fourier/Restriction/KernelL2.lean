import OAI.Analysis.Fourier.Restriction.GramKernel

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem norm_integralKernel_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hbound : ∀ z, ‖K z‖ ≤ M)
    {f : X → ℂ} (hf : Integrable f μ) (y : Y) :
    ‖integralKernel μ K f y‖ ≤ M * ∫ x, ‖f x‖ ∂μ := by
  calc
    _ ≤ ∫ x, ‖K (y, x) * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖f x‖ ∂μ := by
      apply integral_mono (integrable_kernel_mul μ hK hbound hf y).norm (hf.norm.const_mul M)
      intro x
      change ‖K (y, x) * f x‖ ≤ M * ‖f x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem lintegral_sq_eq_enorm_integral_mul_star
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {u : Y → ℂ} (hu : MemLp u 2 ν) :
    (∫⁻ y, ‖u y‖ₑ ^ (2 : ℝ) ∂ν) = ‖∫ y, u y * star (u y) ∂ν‖ₑ := by
  have hi : Integrable (fun y ↦ ‖u y‖ ^ 2) ν := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      hu.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have he (y : Y) : u y * star (u y) = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    change u y * (starRingEnd ℂ) (u y) = ((‖u y‖ ^ 2 : ℝ) : ℂ)
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (u y)
  simp_rw [he]
  rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun y ↦ sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun y ↦ sq_nonneg _))]
  apply lintegral_congr
  intro y
  simp only [ENNReal.rpow_two, pow_two, ← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)]

theorem lintegral_sq_integralKernel_le_of_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, ‖K z‖ ≤ M)
    {B : ℝ≥0∞} (hgram : ∀ x, (∫⁻ z, ‖gramKernel ν K (x, z)‖ₑ ∂μ) ≤ B)
    {f : X → ℂ} (hfm : Measurable f) (hf : Integrable f μ) :
    (∫⁻ y, ‖integralKernel μ K f y‖ₑ ^ (2 : ℝ) ∂ν) ≤
      B * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hT : MemLp (integralKernel μ K f) 2 ν :=
    MemLp.of_bound (measurable_integralKernel μ hK hf.aestronglyMeasurable).aestronglyMeasurable
      (M * ∫ x, ‖f x‖ ∂μ) (Filter.Eventually.of_forall (norm_integralKernel_le μ hK hbound hf))
  rw [lintegral_sq_eq_enorm_integral_mul_star ν hT,
    integralKernel_gram_identity μ ν hK hM hbound hf]
  apply schur_complex_quadratic_bound μ (measurable_gramKernel ν hK) hfm hgram
  intro z
  have he (x : X) : ‖gramKernel ν K (x, z)‖ₑ = ‖gramKernel ν K (z, x)‖ₑ := by
    rw [gramKernel_swap ν K z x]
    simp
  simp_rw [he]
  exact hgram z

theorem lintegral_sq_integralKernel_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, ‖K z‖ ≤ M)
    {B : ℝ≥0∞} (hgram : ∀ x, (∫⁻ z, ‖gramKernel ν K (x, z)‖ₑ ∂μ) ≤ B)
    {f : X → ℂ} (hf : Integrable f μ) :
    (∫⁻ y, ‖integralKernel μ K f y‖ₑ ^ (2 : ℝ) ∂ν) ≤
      B * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g μ := hf.congr hfg
  rw [integralKernel_congr_ae μ K hfg]
  have H := lintegral_sq_integralKernel_le_of_measurable μ ν hK hM hbound hgram
    hf.aestronglyMeasurable.measurable_mk hg
  have he : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  rwa [he] at H

end OAI.Analysis.Fourier.Restriction
