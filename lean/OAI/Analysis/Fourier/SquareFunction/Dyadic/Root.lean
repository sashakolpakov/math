import OAI.Analysis.Fourier.SquareFunction.Dyadic.Local

/-! Separating and controlling the root-average error in the sharp estimate. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral
open scoped ENNReal

theorem positiveSetMean_restrict_of_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {Q I : Set X} (hQ : MeasurableSet Q) (hQI : Q ⊆ I) :
    positiveSetMean (μ.restrict I) f Q = positiveSetMean μ f Q := by
  simp only [positiveSetMean, Measure.restrict_restrict_of_subset hQI,
    Measure.restrict_apply hQ, inter_eq_left.mpr hQI]

theorem setOscillation_restrict_of_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {Q I : Set X} (hQ : MeasurableSet Q) (hQI : Q ⊆ I) :
    setOscillation (μ.restrict I) f Q = setOscillation μ f Q := by
  simp only [setOscillation, positiveSetMean_restrict_of_subset μ f hQ hQI,
    Measure.restrict_restrict_of_subset hQI, Measure.restrict_apply hQ,
    inter_eq_left.mpr hQI]

/-- The root mean contributes an error proportional to the negative power
`measure(root)^(1-p)`, with the global first moment as coefficient. -/
theorem positiveSetMean_root_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) {p : ℝ} (hp : 0 ≤ p) :
    positiveSetMean μ f Q ^ p * μ Q ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ^ p * μ Q ^ (1 - p) := by
  calc
    _ ≤ ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ Q) ^ p * μ Q := by
      apply mul_le_mul_left
      apply ENNReal.rpow_le_rpow _ hp
      exact ENNReal.div_le_div_right (setLIntegral_le_lintegral Q _) (μ Q)
    _ = _ := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hp, ENNReal.rpow_sub _ _ hQ0 hQtop,
        ENNReal.rpow_one]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Splitting the maximum in the local sharp estimate leaves a multiple of
the oscillation majorant's moment and the explicit root-average error. -/
theorem lintegral_max_scaled {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℝ) (_ : ∀ x, 0 ≤ G x)
    {A b γ p : ℝ} (hA : 0 ≤ A) (_ : 0 ≤ b) (hγ : 0 < γ) (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (max (A * (G x / γ)) (A * b)) ^ p ∂μ) ≤
      ENNReal.ofReal (A / γ) ^ p * (∫⁻ x, ENNReal.ofReal (G x) ^ p ∂μ) +
        (ENNReal.ofReal A ^ p * ENNReal.ofReal b ^ p) * μ univ := by
  have hc (x : X) : ENNReal.ofReal (A * (G x / γ)) ^ p =
      ENNReal.ofReal (A / γ) ^ p * ENNReal.ofReal (G x) ^ p := by
    rw [show A * (G x / γ) = (A / γ) * G x by ring,
      ENNReal.ofReal_mul (div_nonneg hA hγ.le), ENNReal.mul_rpow_of_nonneg _ _ hp]
  have hb' : ENNReal.ofReal (A * b) ^ p =
      ENNReal.ofReal A ^ p * ENNReal.ofReal b ^ p := by
    rw [ENNReal.ofReal_mul hA, ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal (A / γ) ^ p * ENNReal.ofReal (G x) ^ p) +
        (ENNReal.ofReal A ^ p * ENNReal.ofReal b ^ p) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rcases le_total (A * (G x / γ)) (A * b) with h | h
      · rw [max_eq_right h, hb']
        exact le_add_of_nonneg_left bot_le
      · rw [max_eq_left h, hc]
        exact le_add_of_nonneg_right bot_le
    _ = _ := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top),
        lintegral_const]

end OAI.Analysis.Fourier.SquareFunction
