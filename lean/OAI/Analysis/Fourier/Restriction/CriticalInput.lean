import OAI.Analysis.Fourier.Restriction.BRFarField

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def restrictionInputExponent (n : ℕ) : ℝ := 2 * (n : ℝ) / ((n : ℝ) + 1)

theorem restrictionInputExponent_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 < restrictionInputExponent n ∧ restrictionInputExponent n < 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold restrictionInputExponent
  constructor
  · apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

theorem div_restrictionInputExponent {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / restrictionInputExponent n = ((n : ℝ) + 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold restrictionInputExponent
  field_simp

theorem bochnerRieszIndex_restrictionInputExponent {n : ℕ} (hn : 2 ≤ n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal (restrictionInputExponent n)) = 0 := by
  have hp := restrictionInputExponent_bounds hn
  have hp0 : 0 < restrictionInputExponent n := by linarith
  have hi : 0 ≤ (restrictionInputExponent n)⁻¹ - 1 / 2 := by
    have : 1 / 2 < 1 / restrictionInputExponent n := by
      exact one_div_lt_one_div_of_lt hp0 hp.2
    simpa only [one_div] using sub_nonneg.mpr this.le
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le, abs_of_nonneg hi]
  have he : (n : ℝ) * ((restrictionInputExponent n)⁻¹ - 1 / 2) - 1 / 2 = 0 := by
    have H := div_restrictionInputExponent hn
    rw [div_eq_mul_inv] at H
    linarith
  rw [he, max_self]

theorem bochnerRiesz_critical_farField (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c D B : ℝ, 0 < c ∧ 0 ≤ D ∧ 0 < B ∧ ∀ R : ℝ, 0 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → MemLp f (ENNReal.ofReal (restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) → ∀ T : ℝ, 2 ≤ T → 2 * R ≤ T → Real.pi / 2 ≤ T →
      ENNReal.ofReal c * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n))
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (B * T ^ δ) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume +
      ENNReal.ofReal (D * (1 + R ^ 2) / T * ∫ y, ‖f y‖) *
        OAI.Analysis.Fourier.Restriction.sphereMeasure n univ ^ (1 / restrictionInputExponent n) := by
  have hp := restrictionInputExponent_bounds hn
  obtain ⟨c, D, hc, hD, H⟩ := bochnerRiesz_farField_norm (by omega : 1 ≤ n) hδ
  obtain ⟨B, hB, HB⟩ := OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_bochnerRiesz_compact_convolution hls hn
    (ENNReal.one_le_ofReal.mpr hp.1.le) ENNReal.ofReal_ne_top
    (show OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal (restrictionInputExponent n)) < δ by
      rw [bochnerRieszIndex_restrictionInputExponent hn]; exact hδ)
  refine ⟨c, D, 2 * 3 ^ (((n : ℝ) + 2 * δ + 1) / 2) * B, hc, hD, by positivity, ?_⟩
  intro R hR f hfm hfi hfp hfs T hT hRT hpi
  have he : ((n : ℝ) + 2 * δ + 1) / 2 - (n : ℝ) / restrictionInputExponent n = δ := by
    rw [div_restrictionInputExponent hn]
    ring
  have H := H R hR f hfm hfi hfs (restrictionInputExponent n) T hp.1.le hT hRT hpi
  rw [he] at H
  have HB := (HB f hfi hfp R hR hfs).2
  change eLpNorm (sphericalKernelConvolution (OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ) f) _ _ ≤ _ at HB
  apply H.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ENNReal.ofReal (2 * 3 ^ (((n : ℝ) + 2 * δ + 1) / 2) * T ^ δ) *
        (ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume) :=
      mul_le_mul' le_rfl HB
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end OAI.Analysis.Fourier.Restriction
