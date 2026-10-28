import OAI.Analysis.Fourier.BochnerRiesz.UnitBound
import OAI.Analysis.Fourier.BochnerRiesz.RadiusDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Local smoothing gives Bochner--Riesz in the full strict range above
two, uniformly over all positive radii. -/
theorem localSmoothing_bochnerRiesz_ge_two (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p) (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hunit⟩ := localSmoothing_bochnerRiesz_unit hls hn hp hδ
  refine ⟨C, hC, ?_⟩
  intro R hR f
  have H := bochnerRiesz_uniform_radius_of_unit (fun g ↦ (hunit g).2) hR f
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), H⟩

theorem bochnerRieszIndex_ofReal_ge_two (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) = OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := by
  have hp0 : 0 ≤ p := by linarith
  have hi : p⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0, abs_of_nonpos (by linarith), max_comm 0]
  congr 1
  ring

theorem localSmoothing_bochnerRiesz_strict_ge_two (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} (hp : 2 ≤ p) (hpt : p ≠ ⊤) {δ : ℝ}
    (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  have hpR : 2 ≤ p.toReal := by
    have H := ENNReal.toReal_mono hpt hp
    norm_num at H
    exact H
  have he : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  have hδR : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p.toReal < δ := by
    rw [← bochnerRieszIndex_ofReal_ge_two n hpR, he]
    exact hδ
  simpa only [he] using localSmoothing_bochnerRiesz_ge_two hls hn hpR hδR

end OAI.Analysis.Fourier.BochnerRiesz
