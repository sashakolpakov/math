import OAI.Analysis.Fourier.Restriction.Interpolation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def amplitudeLow {X : Type*} (f : X → ℂ) (t : ℝ) : X → ℂ :=
  {x | ‖f x‖ ≤ t}.indicator f

def amplitudeHigh {X : Type*} (f : X → ℂ) (t : ℝ) : X → ℂ :=
  {x | t < ‖f x‖}.indicator f

theorem amplitudeHigh_add_low {X : Type*} (f : X → ℂ) (t : ℝ) :
    (fun x ↦ amplitudeHigh f t x + amplitudeLow f t x) = f := by
  funext x
  by_cases hx : ‖f x‖ ≤ t
  · simp [amplitudeHigh, amplitudeLow, hx, not_lt.mpr hx]
  · simp [amplitudeHigh, amplitudeLow, hx, lt_of_not_ge hx]

theorem integrable_amplitudeLow {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ) (t : ℝ) :
    Integrable (amplitudeLow f t) μ :=
  hf1.indicator (measurableSet_le hf.norm measurable_const)

theorem integrable_amplitudeHigh {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ) (t : ℝ) :
    Integrable (amplitudeHigh f t) μ :=
  hf1.indicator (measurableSet_lt measurable_const hf.norm)

theorem enorm_amplitudeLow_le {X : Type*} (f : X → ℂ) {t : ℝ} (_ : 0 ≤ t) (x : X) :
    ‖amplitudeLow f t x‖ₑ ≤ ENNReal.ofReal t := by
  by_cases hx : ‖f x‖ ≤ t
  · simpa [amplitudeLow, hx, ← ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  · simp [amplitudeLow, hx]

theorem memLp_amplitudeLow_two {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (amplitudeLow f t) 2 μ := by
  have hlow := integrable_amplitudeLow hf hf1 t
  have H := eLpNorm_le_of_enorm_bound μ hlow.aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    (Filter.Eventually.of_forall (enorm_amplitudeLow_le f ht))
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at H
  apply H.trans_lt
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (memLp_one_iff_integrable.mpr hlow).eLpNorm_ne_top

theorem lintegral_amplitudeHigh {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) :
    (∫⁻ x, ‖amplitudeHigh f t x‖ₑ ∂μ) = ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ := by
  rw [← lintegral_indicator (measurableSet_lt measurable_const hf.norm)]
  congr 1
  funext x
  by_cases hx : t < ‖f x‖ <;> simp [amplitudeHigh, hx]

theorem lintegral_amplitudeLow_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) :
    (∫⁻ x, ‖amplitudeLow f t x‖ₑ ^ (2 : ℝ) ∂μ) =
      ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [← lintegral_indicator (measurableSet_le hf.norm measurable_const)]
  congr 1
  funext x
  by_cases hx : ‖f x‖ ≤ t <;> simp [amplitudeLow, hx]

end OAI.Analysis.Fourier.Restriction
