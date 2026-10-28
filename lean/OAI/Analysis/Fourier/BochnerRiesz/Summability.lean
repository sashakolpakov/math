import OAI.Analysis.Fourier.BochnerRiesz.L1Strong
import OAI.Analysis.Fourier.BochnerRiesz.TopExtension
import OAI.Analysis.Fourier.BochnerRiesz.FullSummability
import OAI.Analysis.Fourier.BochnerRiesz.ExtensionUnique

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


/-- The full finite-`p` norm-summability consequence, including `p=1`. -/
theorem localSmoothing_bochnerRiesz_norm_summability (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ⊤)
    {δ : ℝ} (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) → BrLp n p →L[ℂ] BrLp n p,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) ∧
      (∀ f, Tendsto (fun R : ℝ => brLpRadius T R f) atTop (𝓝 f)) := by
  by_cases hp1 : p = 1
  · subst p
    rw [OAI.Analysis.Fourier.Radial.bochnerRieszIndex_one (by omega)] at hδ
    exact bochnerRiesz_L1_strong_convergence (by omega) hδ
  have hp : 1 < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)
  have hpR : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr hp
  obtain ⟨q, hq, he⟩ : ∃ q : ℝ, 1 < q ∧ p = ENNReal.ofReal q :=
    ⟨p.toReal, hpR, (ENNReal.ofReal_toReal hpt).symm⟩
  subst p
  exact localSmoothing_bochnerRiesz_Lp_strong_convergence hls hn hq hδ

/-- Full bounded linear realizations for every exponent, including `∞`.
At `∞`, they are defined by the actual integrable convolution kernel. -/
theorem localSmoothing_bochnerRiesz_all_Lp_operators (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) → BrLp n p →L[ℂ] BrLp n p,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) := by
  by_cases hpt : p = ⊤
  · subst p
    rw [OAI.Analysis.Fourier.Radial.bochnerRieszIndex_top (by omega)] at hδ
    obtain ⟨C, hC, T, hT, _, hs⟩ := bochnerRiesz_Linfty_operators (by omega) hδ
    exact ⟨C, hC, T, hT, hs⟩
  exact localSmoothing_bochnerRiesz_Lp_operators hls hn hpt hδ

end OAI.Analysis.Fourier.BochnerRiesz
