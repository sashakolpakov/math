import OAI.Analysis.Fourier.SquareFunction.Shell.MixedBound
import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

/-! A smooth annular projection makes the mixed thin-shell estimate apply
to every Schwartz input, with no Fourier-support condition on that input. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

theorem localSmoothing_projected_thinShell_mixed (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (thinShellSquareNorm φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f))
        (ENNReal.ofReal p) volume ∧
      eLpNorm (thinShellSquareNorm φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f))
        (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbase⟩ := localSmoothing_thinShell_mixed hls hn hψ hcψ hzero φ hp hε
  obtain ⟨A, hA, hproj⟩ := OAI.Analysis.Fourier.BochnerRiesz.annularProject_uniform_bound hχ hcχ
  refine ⟨C * ENNReal.ofReal A, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top, ?_⟩
  intro δ hδ hδone f
  have hs : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) ξ ≠ 0 → ψ ξ = 1 := by
    simpa only [one_smul] using OAI.Analysis.Fourier.BochnerRiesz.annularProject_support_cutoff hχ hcχ
      (by norm_num : (0 : ℝ) < 1) f hcut
  have hb := hbase δ hδ hδone (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) hs
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hnorm := hproj 1 (by norm_num) f (ENNReal.ofReal p) hpone ENNReal.ofReal_ne_top
  calc
    _ ≤ (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
        (ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume) := mul_le_mul_right hnorm _
    _ = _ := by ac_rfl

end OAI.Analysis.Fourier.SquareFunction
