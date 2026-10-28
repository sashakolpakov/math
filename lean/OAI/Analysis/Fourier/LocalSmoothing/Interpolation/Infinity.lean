import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Operator

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation


/-- Interpolation with a normalized infinity endpoint. Its finite endpoint
constant occurs to the exact power needed for the sharp frequency exponent. -/
theorem operator_infinity_moment_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p q : ℝ} (hq : 0 < q) (hqp : q < p) {A : ℝ≥0∞}
    (hqbound : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ^ q ∂μ)
    (hinf : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖T g y‖ ≤ t)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ) (hfq : MemLp f (.ofReal q) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      2 * (A * .ofReal (p / (p - q))) ^ (1 / p) * eLpNorm f (.ofReal p) μ := by
  have hp : 0 < p := hq.trans hqp
  apply OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_half_moment μ ν hf.aestronglyMeasurable (hTm f hf hfi) hp
  have H := power_moment_le_of_tail μ ν hf.norm ((hTm f hf hfi).norm.div_const 2)
    (fun x => norm_nonneg _) (fun y => by positivity) hq hqp (A := A)
  simp only [ofReal_norm] at H
  apply H
  intro t ht
  have hsH : MeasurableSet {x | t < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hsL : MeasurableSet {x | ‖f x‖ ≤ t} := measurableSet_le hf.norm measurable_const
  have hmH : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) := hf.indicator hsH
  have hmL : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) := hf.indicator hsL
  have hiH := OAI.Analysis.Fourier.Restriction.integrable_amplitudeHigh hf hfi t
  have hiL := OAI.Analysis.Fourier.Restriction.integrable_amplitudeLow hf hfi t
  have hH := hqbound _ hmH hiH (hfq.indicator hsH)
  have hL := hinf _ hmL hiL t ht (fun x => by
    by_cases hx : ‖f x‖ ≤ t
    · simp [OAI.Analysis.Fourier.Restriction.amplitudeLow, hx]
    · simpa [OAI.Analysis.Fourier.Restriction.amplitudeLow, hx] using ht.le)
  calc
    _ ≤ ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} := by
      apply measure_mono_ae
      filter_upwards [hL] with y hlow
      intro hy
      have he := hadd (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) hiH hiL y
      rw [OAI.Analysis.Fourier.Restriction.amplitudeHigh_add_low] at he
      have hn := norm_add_le (T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y) (T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y)
      rw [← he] at hn
      change t < ‖T f y‖ / 2 at hy
      change t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖
      linarith
    _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ₑ ^ q ∂ν) / .ofReal t ^ q :=
      OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmH hiH) hq ht
    _ ≤ (A * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q ∂μ) / .ofReal t ^ q := by gcongr
    _ = _ := by rw [moment_amplitudeHigh μ hf t hq]; simp only [div_eq_mul_inv]; ring

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
