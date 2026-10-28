import OAI.Analysis.Fourier.BochnerRiesz.DualBound
import OAI.Analysis.Fourier.BochnerRiesz.InteriorUniform
import OAI.Analysis.Fourier.BochnerRiesz.StrictRange

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem bochnerRieszIndex_ofReal_le_two (n : ℕ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) = OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n (p / (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hi : 1 / 2 ≤ p⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hp0 hp2
  have hpq : p.HolderConjugate (p / (p - 1)) := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hqi : (p / (p - 1))⁻¹ = 1 - p⁻¹ := by
    have H := (Real.holderConjugate_iff.mp hpq).2
    linarith
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le, abs_of_nonneg (by linarith), max_comm 0]
  rw [show (n : ℝ) / (p / (p - 1)) = (n : ℝ) * (1 - p⁻¹) by rw [div_eq_mul_inv, hqi]]
  congr 1
  ring

/-- The conjugate-exponent argument extends the Bochner--Riesz implication
to every strict exponent between one and two. -/
theorem localSmoothing_bochnerRiesz_le_two (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hq2 : 2 ≤ p / (p - 1) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hδq : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n (p / (p - 1)) < δ := by
    rwa [← bochnerRieszIndex_ofReal_le_two n hp hp2]
  have hδ0 : 0 < δ := lt_of_le_of_lt (le_max_left _ _) hδq
  obtain ⟨J, hJ, C, hC, hpartial⟩ := localSmoothing_brInteriorCycles_uniform hls hn hq2 hδq
  have hunit (f : SchwartzMap (Space n) ℂ) :
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
    apply eLpNorm_le_of_tendsto_pointwise volume
      (fun N ↦ (continuous_brInteriorCycles hδ0 (show 2 ≤ J + N by omega) f).aestronglyMeasurable)
      (continuous_bochnerRiesz_schwartz hδ0.le 1 f).aestronglyMeasurable
      (tendsto_brInteriorCycles hδ0 hJ f) (by linarith)
    intro N
    exact brInteriorCycles_dual_bound hδ0 (by omega) hp (hpartial N) f
  refine ⟨C, hC, ?_⟩
  intro R hR f
  have H := bochnerRiesz_uniform_radius_of_unit hunit hR f
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), H⟩

/-- Local smoothing implies the Bochner--Riesz conjecture throughout the
conjectured strict range for all finite exponents strictly greater than one. -/
theorem localSmoothing_bochnerRiesz_strict_finite (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ⊤) {δ : ℝ}
    (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  by_cases hp2 : 2 ≤ p
  · exact localSmoothing_bochnerRiesz_strict_ge_two hls hn hp2 hpt hδ
  have he : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  have hpR : 1 < p.toReal := by
    by_contra h
    have H := ENNReal.ofReal_le_ofReal (le_of_not_gt h)
    rw [he, ENNReal.ofReal_one] at H
    exact (not_le_of_gt hp) H
  have hpR2 : p.toReal ≤ 2 := by
    have H := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (le_of_not_ge hp2)
    simpa using H
  have hδR : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p.toReal) < δ := by simpa only [he] using hδ
  simpa only [he] using localSmoothing_bochnerRiesz_le_two hls hn hpR hpR2 hδR

end OAI.Analysis.Fourier.BochnerRiesz
