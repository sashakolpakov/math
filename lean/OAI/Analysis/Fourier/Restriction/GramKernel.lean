import OAI.Analysis.Fourier.Restriction.IntegralKernel

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def gramKernel {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (K : Y × X → ℂ) (w : X × X) : ℂ :=
  ∫ y, K (y, w.1) * star (K (y, w.2)) ∂ν

theorem gramKernel_swap {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (K : Y × X → ℂ) (x z : X) :
    gramKernel ν K (z, x) = star (gramKernel ν K (x, z)) := by
  unfold gramKernel
  change _ = (starRingEnd ℂ) (∫ y, K (y, x) * star (K (y, z)) ∂ν)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [mul_comm]

theorem measurable_gramKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {K : Y × X → ℂ} (hK : Measurable K) :
    Measurable (gramKernel ν K) := by
  have hm : StronglyMeasurable (fun z : (X × X) × Y ↦
      K (z.2, z.1.1) * star (K (z.2, z.1.2))) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact hm.integral_prod_right'.measurable

theorem integralKernel_mul_star {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (K : Y × X → ℂ) (f : X → ℂ) (y : Y) :
    integralKernel μ K f y * star (integralKernel μ K f y) =
      ∫ w : X × X, (K (y, w.1) * f w.1) * star (K (y, w.2) * f w.2) ∂μ.prod μ := by
  unfold integralKernel
  change (∫ x, K (y, x) * f x ∂μ) *
    (starRingEnd ℂ) (∫ x, K (y, x) * f x ∂μ) = _
  rw [← integral_conj]
  exact (integral_prod_mul _ _).symm

theorem integrable_gram_integrand
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, ‖K z‖ ≤ M)
    {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun z : Y × (X × X) ↦
      (K (z.1, z.2.1) * f z.2.1) * star (K (z.1, z.2.2) * f z.2.2))
      (ν.prod (μ.prod μ)) := by
  have hdom : Integrable (fun z : Y × (X × X) ↦ M ^ 2 * (‖f z.2.1‖ * ‖f z.2.2‖))
      (ν.prod (μ.prod μ)) :=
    (integrable_const (M ^ 2 : ℝ)).mul_prod (hf.norm.mul_prod hf.norm)
  have hF1 : AEStronglyMeasurable (fun z : Y × (X × X) ↦ f z.2.1) (ν.prod (μ.prod μ)) :=
    hf.aestronglyMeasurable.comp_fst.comp_snd
  have hF2 : AEStronglyMeasurable (fun z : Y × (X × X) ↦ f z.2.2) (ν.prod (μ.prod μ)) :=
    hf.aestronglyMeasurable.comp_snd.comp_snd
  have hK1 : Measurable (fun z : Y × (X × X) ↦ K (z.1, z.2.1)) := by fun_prop
  have hK2 : Measurable (fun z : Y × (X × X) ↦ K (z.1, z.2.2)) := by fun_prop
  apply hdom.mono' ((hK1.aestronglyMeasurable.mul hF1).mul (hK2.aestronglyMeasurable.mul hF2).star)
  filter_upwards [] with z
  change ‖(K (z.1, z.2.1) * f z.2.1) * star (K (z.1, z.2.2) * f z.2.2)‖ ≤
    M ^ 2 * (‖f z.2.1‖ * ‖f z.2.2‖)
  simp only [norm_mul, norm_star]
  calc
    _ ≤ (M * ‖f z.2.1‖) * (M * ‖f z.2.2‖) := by gcongr <;> apply hbound
    _ = _ := by ring

/-- The `TT*` identity for the actual integral operator, justified by
absolute integrability of the three-variable integrand. -/
theorem integralKernel_gram_identity
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, ‖K z‖ ≤ M)
    {f : X → ℂ} (hf : Integrable f μ) :
    (∫ y, integralKernel μ K f y * star (integralKernel μ K f y) ∂ν) =
      ∫ w : X × X, f w.1 * star (f w.2) * gramKernel ν K w ∂μ.prod μ := by
  calc
    _ = ∫ y, (∫ w : X × X,
        (K (y, w.1) * f w.1) * star (K (y, w.2) * f w.2) ∂μ.prod μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact integralKernel_mul_star μ K f y
    _ = ∫ w : X × X, (∫ y,
        (K (y, w.1) * f w.1) * star (K (y, w.2) * f w.2) ∂ν) ∂μ.prod μ :=
      integral_integral_swap (integrable_gram_integrand μ ν hK hM hbound hf)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [gramKernel, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [star_mul]
      ring

end OAI.Analysis.Fourier.Restriction
