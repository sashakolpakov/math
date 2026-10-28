import OAI.Analysis.Fourier.Restriction.Markov
import OAI.Analysis.Fourier.Restriction.Truncation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The actual truncation argument for an additive operator with strong
`L¹` and `L²` bounds. The second constant is the square-energy constant.
No target integrability is assumed. -/
theorem operator_half_moment_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x ↦ g x + h x) y = T g y + T h y)
    {A B : ℝ≥0∞}
    (h1 : ∀ g, Integrable g μ → (∫⁻ y, ‖T g y‖ₑ ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (h2 : ∀ g, Integrable g μ → MemLp g 2 μ →
      (∫⁻ y, ‖T g y‖ₑ ^ (2 : ℝ) ∂ν) ≤ B * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ)
    {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    (∫⁻ y, ENNReal.ofReal (‖T f y‖ / 2) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - 1)) + B * ENNReal.ofReal (p / (2 - p))) *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have H := power_moment_le_of_two_truncations μ ν hf.norm
    ((hTm f hf1).norm.div_const 2) (fun x ↦ norm_nonneg _) (fun y ↦ by positivity) hp hp2
      (A := A) (B := B)
  simp only [ofReal_norm] at H
  apply H
  intro t ht
  have hhi := integrable_amplitudeHigh hf hf1 t
  have hlo := integrable_amplitudeLow hf hf1 t
  have hlo2 := memLp_amplitudeLow_two hf hf1 ht.le
  have htriangle (y : Y) : ‖T f y‖ ≤
      ‖T (amplitudeHigh f t) y‖ + ‖T (amplitudeLow f t) y‖ := by
    have heq := hadd (amplitudeHigh f t) (amplitudeLow f t) hhi hlo y
    rw [amplitudeHigh_add_low] at heq
    rw [heq]
    exact norm_add_le _ _
  have hhigh : ν {y | t < ‖T (amplitudeHigh f t) y‖} ≤
      A / ENNReal.ofReal t * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ := by
    have HM := measure_norm_gt_le_moment ν (hTm _ hhi) (by norm_num : (0 : ℝ) < 1) ht
    simp only [ENNReal.rpow_one] at HM
    calc
      _ ≤ (∫⁻ y, ‖T (amplitudeHigh f t) y‖ₑ ∂ν) / ENNReal.ofReal t := HM
      _ ≤ (A * ∫⁻ x, ‖amplitudeHigh f t x‖ₑ ∂μ) / ENNReal.ofReal t := by gcongr; exact h1 _ hhi
      _ = _ := by rw [lintegral_amplitudeHigh μ hf]; simp only [div_eq_mul_inv]; ring
  have hlow : ν {y | t < ‖T (amplitudeLow f t) y‖} ≤
      B / ENNReal.ofReal t ^ (2 : ℝ) *
        ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    calc
      _ ≤ (∫⁻ y, ‖T (amplitudeLow f t) y‖ₑ ^ (2 : ℝ) ∂ν) / ENNReal.ofReal t ^ (2 : ℝ) :=
        measure_norm_gt_le_moment ν (hTm _ hlo) (by norm_num) ht
      _ ≤ (B * ∫⁻ x, ‖amplitudeLow f t x‖ₑ ^ (2 : ℝ) ∂μ) /
          ENNReal.ofReal t ^ (2 : ℝ) := by gcongr; exact h2 _ hlo hlo2
      _ = _ := by rw [lintegral_amplitudeLow_sq μ hf]; simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ν ({y | t < ‖T (amplitudeHigh f t) y‖} ∪ {y | t < ‖T (amplitudeLow f t) y‖}) := by
      apply measure_mono
      intro y hy
      change t < ‖T f y‖ / 2 at hy
      by_contra hc
      have hc' := not_or.mp hc
      have hh : ‖T (amplitudeHigh f t) y‖ ≤ t := le_of_not_gt hc'.1
      have hl : ‖T (amplitudeLow f t) y‖ ≤ t := le_of_not_gt hc'.2
      have := htriangle y
      linarith
    _ ≤ ν {y | t < ‖T (amplitudeHigh f t) y‖} + ν {y | t < ‖T (amplitudeLow f t) y‖} :=
      measure_union_le _ _
    _ ≤ _ := add_le_add hhigh hlow

theorem eLpNorm_le_of_half_moment
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    {f : X → ℂ} {u : Y → ℂ} (hf : AEStronglyMeasurable f μ) (hu : Measurable u)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (h : (∫⁻ y, ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν) ≤
      C * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    eLpNorm u (ENNReal.ofReal p) ν ≤
      2 * C ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hm : Measurable (fun y ↦ ENNReal.ofReal (‖u y‖ / 2) ^ p) :=
    (hu.norm.div_const 2).ennreal_ofReal.pow_const p
  have H : eLpNorm u (ENNReal.ofReal p) ν ^ p ≤
      ((2 : ℝ≥0∞) ^ p * C) * eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hf]
    calc
      _ = ∫⁻ y, (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν := by
        apply lintegral_congr
        intro y
        have hx : ENNReal.ofReal ‖u y‖ = ENNReal.ofReal (2 : ℝ) *
            ENNReal.ofReal (‖u y‖ / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [ofReal_norm, ENNReal.ofReal_ofNat] at hx
        rw [hx, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = (2 : ℝ≥0∞) ^ p * ∫⁻ y, ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν :=
        lintegral_const_mul _ hm
      _ ≤ (2 : ℝ≥0∞) ^ p * (C * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by gcongr
      _ = _ := by ring
  have H' := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hp))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hp)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'

/-- A strong `Lᵖ` interpolation estimate for `1 < p < 2`, obtained
directly from additive decomposition and the endpoint energy estimates. -/
theorem eLpNorm_operator_le_of_L1_L2
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x ↦ g x + h x) y = T g y + T h y)
    {A B : ℝ≥0∞}
    (h1 : ∀ g, Integrable g μ → (∫⁻ y, ‖T g y‖ₑ ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (h2 : ∀ g, Integrable g μ → MemLp g 2 μ →
      (∫⁻ y, ‖T g y‖ₑ ^ (2 : ℝ) ∂ν) ≤ B * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ)
    {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤
      2 * (A * ENNReal.ofReal (p / (p - 1)) + B * ENNReal.ofReal (p / (2 - p))) ^ (1 / p) *
        eLpNorm f (ENNReal.ofReal p) μ :=
  eLpNorm_le_of_half_moment μ ν hf.aestronglyMeasurable (hTm f hf1) (by linarith)
    (operator_half_moment_le μ ν T hTm hadd h1 h2 hf hf1 hp hp2)

end OAI.Analysis.Fourier.Restriction
