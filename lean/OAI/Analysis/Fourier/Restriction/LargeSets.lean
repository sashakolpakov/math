import OAI.Analysis.Fourier.Restriction.RestrictedBand
import OAI.Analysis.Fourier.Restriction.BoundedInput

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem enorm_angularFourier_le {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  apply (enorm_integral_le_lintegral_enorm _).trans_eq
  apply lintegral_congr
  intro x
  simp [← ofReal_norm, Complex.norm_exp]

theorem angularFourier_bounded_input_trivial {n : ℕ} {p : ℝ} (hp : 0 < p)
    {E : Set (Space n)} (hE : MeasurableSet E) (hEt : volume E ≠ ⊤)
    {f : Space n → ℂ} (hf : Integrable f) (hfb : ∀ x, ‖f x‖ ≤ 1)
    (hfs : ∀ x, x ∉ E → f x = 0) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      volume E * (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ) ^ (1 / p) := by
  have H1 := eLpNorm_le_bound_mul_measure volume hf.aestronglyMeasurable hE
    (by norm_num : (0 : ℝ) ≤ 1) hfb hfs (by norm_num : (0 : ℝ) < 1)
  simp only [ENNReal.ofReal_one, one_div_one, ENNReal.rpow_one, one_mul] at H1
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable] at H1
  have Hb (ξ : Space n) : ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖ ≤ (volume E).toReal := by
    have H := (enorm_angularFourier_le f ξ).trans H1
    simpa only [toReal_enorm] using ENNReal.toReal_mono hEt H
  have H := eLpNorm_le_bound_mul_measure (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (continuous_angularFourier hf).aestronglyMeasurable (E := Set.univ) MeasurableSet.univ
    ENNReal.toReal_nonneg Hb (by intro x hx; simp at hx) hp
  simpa only [ENNReal.ofReal_toReal hEt] using H

/-- A support-size power bound for sets of measure at least one extends to
all sets; the small sets are handled by the elementary `L1` estimate. -/
theorem restrictedFourierBound_of_large_sets {n : ℕ} {p r α : ℝ}
    (hp : 0 < p) (hr : 1 ≤ r) (hα : α ≤ 1 / r) {C : ℝ≥0∞}
    (hlarge : ∀ E : Set (Space n), MeasurableSet E → volume E ≠ ⊤ → 1 ≤ volume E →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
        (∀ x, ‖f x‖ ≤ 1) → (∀ x, x ∉ E → f x = 0) →
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ C * (volume E) ^ α) :
    RestrictedFourierBound n r (ENNReal.ofReal p)
      (C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ) ^ (1 / p)) := by
  intro E hE hEt f hfm hfi hfb hfs
  by_cases hE1 : 1 ≤ volume E
  · calc
      _ ≤ C * (volume E) ^ α := hlarge E hE hEt hE1 f hfm hfi hfb hfs
      _ ≤ C * (volume E) ^ (1 / r) := by
        gcongr
      _ ≤ _ := by gcongr; exact le_add_right le_rfl
  · have hpow : volume E ≤ (volume E) ^ (1 / r) := by
      have H := ENNReal.rpow_le_rpow_of_exponent_ge (le_of_lt (lt_of_not_ge hE1))
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr)
      simpa only [one_div_one, ENNReal.rpow_one] using H
    calc
      _ ≤ volume E * (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ) ^ (1 / p) :=
        angularFourier_bounded_input_trivial hp hE hEt hfi hfb hfs
      _ ≤ (volume E) ^ (1 / r) * (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ) ^ (1 / p) := by gcongr
      _ ≤ _ := by
        rw [mul_comm]
        gcongr
        exact le_add_left le_rfl

end OAI.Analysis.Fourier.Restriction
