import OAI.Analysis.Fourier.Restriction.Schur

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def integralKernel {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : Y × X → ℂ) (f : X → ℂ) (y : Y) : ℂ :=
  ∫ x, K (y, x) * f x ∂μ

theorem integralKernel_congr_ae {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : Y × X → ℂ) {f g : X → ℂ} (h : f =ᵐ[μ] g) :
    integralKernel μ K f = integralKernel μ K g := by
  funext y
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem measurable_integralKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] {K : Y × X → ℂ} (hK : Measurable K)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    Measurable (integralKernel μ K f) := by
  rw [integralKernel_congr_ae μ K hf.ae_eq_mk]
  have hm : StronglyMeasurable (fun z : Y × X ↦ K z * hf.mk f z.2) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact hm.integral_prod_right'.measurable

theorem integrable_kernel_mul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hbound : ∀ z, ‖K z‖ ≤ M)
    {f : X → ℂ} (hf : Integrable f μ) (y : Y) :
    Integrable (fun x ↦ K (y, x) * f x) μ := by
  have hKm : Measurable (fun x ↦ K (y, x)) := by fun_prop
  apply (hf.norm.const_mul M).mono' (hKm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖K (y, x) * f x‖ ≤ M * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound (y, x)) (norm_nonneg _)

theorem integralKernel_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hbound : ∀ z, ‖K z‖ ≤ M)
    {f g : X → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (y : Y) :
    integralKernel μ K (fun x ↦ f x + g x) y =
      integralKernel μ K f y + integralKernel μ K g y := by
  simp only [integralKernel, mul_add]
  exact integral_add (integrable_kernel_mul μ hK hbound hf y)
    (integrable_kernel_mul μ hK hbound hg y)

theorem lintegral_integralKernel_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {A : ℝ≥0∞} (hcol : ∀ x, (∫⁻ y, ‖K (y, x)‖ₑ ∂ν) ≤ A) :
    (∫⁻ y, ‖integralKernel μ K f y‖ₑ ∂ν) ≤ A * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hm : AEMeasurable (fun z : Y × X ↦ ‖K z‖ₑ * ‖f z.2‖ₑ) (ν.prod μ) :=
    hK.enorm.aemeasurable.mul hf.comp_snd.enorm
  calc
    _ ≤ ∫⁻ y, ∫⁻ x, ‖K (y, x)‖ₑ * ‖f x‖ₑ ∂μ ∂ν := by
      apply lintegral_mono
      intro y
      simpa only [integralKernel, enorm_mul] using
        (enorm_integral_le_lintegral_enorm (fun x ↦ K (y, x) * f x) (μ := μ))
    _ = ∫⁻ x, ∫⁻ y, ‖K (y, x)‖ₑ * ‖f x‖ₑ ∂ν ∂μ := lintegral_lintegral_swap hm
    _ ≤ ∫⁻ x, A * ‖f x‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      change (∫⁻ y, ‖K (y, x)‖ₑ * ‖f x‖ₑ ∂ν) ≤ A * ‖f x‖ₑ
      have hKm : Measurable (fun y ↦ ‖K (y, x)‖ₑ) := by fun_prop
      rw [lintegral_mul_const _ hKm]
      exact mul_le_mul (hcol x) le_rfl zero_le zero_le
    _ = _ := lintegral_const_mul'' _ hf.enorm

end OAI.Analysis.Fourier.Restriction
