import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Weak
import OAI.Analysis.Fourier.Restriction.OperatorInterpolation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation


theorem moment_amplitudeHigh {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q ∂μ) =
      ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator (measurableSet_lt measurable_const hf.norm)]
  congr 1
  funext x
  by_cases hx : t < ‖f x‖ <;> simp [OAI.Analysis.Fourier.Restriction.amplitudeHigh,hx,hq]

theorem moment_amplitudeLow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow f t x‖ₑ ^ q ∂μ) =
      ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator (measurableSet_le hf.norm measurable_const)]
  congr 1
  funext x
  by_cases hx : ‖f x‖ ≤ t <;> simp [OAI.Analysis.Fourier.Restriction.amplitudeLow,hx,hq]

/-- Strong interpolation between arbitrary finite endpoints, by actual
amplitude truncations. The endpoint constants here are moment constants. -/
theorem operator_two_moment_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p q₀ q₁ : ℝ} (hq₀ : 0 < q₀) (h₀p : q₀ < p) (hp₁ : p < q₁)
    {A B : ℝ≥0∞}
    (h0 : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ → MemLp g (.ofReal q₁) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q₀ ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ^ q₀ ∂μ)
    (h1 : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ → MemLp g (.ofReal q₁) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q₁ ∂ν) ≤ B * ∫⁻ x, ‖g x‖ₑ ^ q₁ ∂μ)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf0 : MemLp f (.ofReal q₀) μ) (hf1 : MemLp f (.ofReal q₁) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      2 * (A * .ofReal (p / (p - q₀)) + B * .ofReal (p / (q₁ - p))) ^ (1 / p) *
        eLpNorm f (.ofReal p) μ := by
  have hp : 0 < p := hq₀.trans h₀p
  have hq₁ : 0 < q₁ := hp.trans hp₁
  apply OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_half_moment μ ν hf.aestronglyMeasurable (hTm f hf hfi) hp
  have H := power_moment_le_of_two_tails μ ν hf.norm ((hTm f hf hfi).norm.div_const 2)
    (fun x => norm_nonneg _) (fun y => by positivity) hq₀ h₀p hp₁ (A := A) (B := B)
  simp only [ofReal_norm] at H
  apply H
  intro t ht
  have hsH : MeasurableSet {x | t < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hsL : MeasurableSet {x | ‖f x‖ ≤ t} := measurableSet_le hf.norm measurable_const
  have hmH : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) := hf.indicator hsH
  have hmL : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) := hf.indicator hsL
  have hiH := OAI.Analysis.Fourier.Restriction.integrable_amplitudeHigh hf hfi t
  have hiL := OAI.Analysis.Fourier.Restriction.integrable_amplitudeLow hf hfi t
  have hH := h0 _ hmH hiH (hf0.indicator hsH) (hf1.indicator hsH)
  have hL := h1 _ hmL hiL (hf0.indicator hsL) (hf1.indicator hsL)
  have high : ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} ≤
      A / .ofReal t ^ q₀ * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ q₀ ∂μ := by
    calc
      _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ₑ ^ q₀ ∂ν) / .ofReal t ^ q₀ :=
        OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmH hiH) hq₀ ht
      _ ≤ (A * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q₀ ∂μ) / .ofReal t ^ q₀ := by gcongr
      _ = _ := by rw [moment_amplitudeHigh μ hf t hq₀]; simp only [div_eq_mul_inv]; ring
  have low : ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖} ≤
      B / .ofReal t ^ q₁ * ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ q₁ ∂μ := by
    calc
      _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖ₑ ^ q₁ ∂ν) / .ofReal t ^ q₁ :=
        OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmL hiL) hq₁ ht
      _ ≤ (B * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow f t x‖ₑ ^ q₁ ∂μ) / .ofReal t ^ q₁ := by gcongr
      _ = _ := by rw [moment_amplitudeLow μ hf t hq₁]; simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ν ({y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} ∪ {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖}) := by
      apply measure_mono
      intro y hy
      have he := hadd (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) hiH hiL y
      rw [OAI.Analysis.Fourier.Restriction.amplitudeHigh_add_low] at he
      have hn := norm_add_le (T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y) (T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y)
      rw [← he] at hn
      by_contra hc
      have hc' := not_or.mp hc
      have hh : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ ≤ t := le_of_not_gt hc'.1
      have hl : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖ ≤ t := le_of_not_gt hc'.2
      change t < ‖T f y‖ / 2 at hy
      linarith
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add high low)

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
