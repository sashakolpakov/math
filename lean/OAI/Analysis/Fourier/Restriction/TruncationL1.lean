import OAI.Analysis.Fourier.Restriction.TruncationMoments
import OAI.Analysis.Fourier.Restriction.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A normalized higher moment controls the first moment on a finite measure
space. The elementary threshold-one split avoids any endpoint convention. -/
theorem lintegral_enorm_le_measure_add_one
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (hf : Measurable f) {a : ℝ} (ha : 1 ≤ a)
    (hfn : (∫⁻ x, ‖f x‖ₑ ^ a ∂μ) ≤ 1) :
    (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ μ univ + 1 := by
  have hhigh : (∫⁻ x, ‖amplitudeHigh f 1 x‖ₑ ∂μ) ≤ 1 := by
    have H := lintegral_amplitudeHigh_le_moment μ hf (by norm_num : (0 : ℝ) < 1) ha
    simpa only [Real.one_rpow, ENNReal.ofReal_one, one_mul] using H.trans (by
      simpa only [Real.one_rpow, ENNReal.ofReal_one, one_mul] using hfn)
  have hlow : (∫⁻ x, ‖amplitudeLow f 1 x‖ₑ ∂μ) ≤ μ univ := by
    calc
      _ ≤ ∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun x ↦ by
        simpa only [ENNReal.ofReal_one] using enorm_amplitudeLow_le f (by norm_num : (0 : ℝ) ≤ 1) x
      _ = _ := by simp
  calc
    _ ≤ ∫⁻ x, ‖amplitudeHigh f 1 x‖ₑ + ‖amplitudeLow f 1 x‖ₑ ∂μ :=
      lintegral_mono fun x ↦ by
        conv_lhs => rw [← amplitudeHigh_add_low f 1]
        exact enorm_add_le _ _
    _ = (∫⁻ x, ‖amplitudeHigh f 1 x‖ₑ ∂μ) +
        ∫⁻ x, ‖amplitudeLow f 1 x‖ₑ ∂μ :=
      lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf.norm)).enorm _
    _ ≤ 1 + μ univ := add_le_add hhigh hlow
    _ = _ := add_comm _ _

theorem norm_sphericalExtension_le_of_normalized_moment
    {n : ℕ} {g : Space n → ℂ} (hg : Measurable g) {a : ℝ} (ha : 1 ≤ a)
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ 1) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ).toReal + 1 := by
  have H := (enorm_sphericalExtension_le g x).trans
    (lintegral_enorm_le_measure_add_one (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hg ha hgn)
  have ht : OAI.Analysis.Fourier.Restriction.sphereMeasure n univ + 1 ≠ (⊤ : ℝ≥0∞) := by finiteness
  have Hr := ENNReal.toReal_mono ht H
  simpa [ENNReal.toReal_add (measure_ne_top _ _) (by simp : (1 : ℝ≥0∞) ≠ ⊤)] using Hr

end OAI.Analysis.Fourier.Restriction
