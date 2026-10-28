import OAI.Analysis.Fourier.SquareFunction.Amplitude.Lp

open OAI.Analysis.Fourier.Wave

/-! Actual amplitude-shell operator estimates: Plancherel at `p = 2`, and
local smoothing for general finite `p ≥ 2`. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal ContDiff

theorem amplitudeShellHilbert_two_bound {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (amplitudeShellHilbert A hA.continuous φ δ f) 2 volume ≤
        (ENNReal.ofReal δ ^ (1 / 2 : ℝ) * C) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hc
  refine ⟨separationMass * ENNReal.ofReal C * eLpNorm φ 2 volume,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top separationMass_ne_top ENNReal.ofReal_ne_top)
      (φ.memLp 2).ne, ?_⟩
  intro δ hδ f
  have hs := eLpNorm_amplitudeShellHilbert_synthesis hA hc φ δ f (p := 2) (by norm_num)
    (B := ENNReal.ofReal C * (ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume) *
      eLpNorm f 2 volume) (fun η => ?_)
  · simpa only [ENNReal.ofReal_ofNat, mul_assoc, mul_comm, mul_left_comm] using hs
  norm_num only [ENNReal.ofReal_ofNat]
  calc
    _ ≤ ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume *
        eLpNorm (amplitudeInput A η f) 2 volume := thinShellHilbert_two_bound φ hδ _
    _ ≤ ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume *
        (ENNReal.ofReal (C * (1 + |η|) ^ (-2 : ℝ)) * eLpNorm f 2 volume) :=
      mul_le_mul' le_rfl ((hb η).2 f 2 (by norm_num) (by norm_num))
    _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl

theorem localSmoothing_amplitudeShellHilbert (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    {χ ψ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzψ : (0 : Space n) ∉ tsupport ψ)
    (hχψ : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (hAχ : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (amplitudeShellHilbert A hA.continuous φ δ f) (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hcA
  obtain ⟨D, hD, hd⟩ := localSmoothing_projected_thinShellHilbert hls hn hχ hcχ hψ hcψ
    hzψ hχψ φ hp hε
  refine ⟨separationMass * ENNReal.ofReal C * D,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top separationMass_ne_top ENNReal.ofReal_ne_top) hD, ?_⟩
  intro δ hδ hδone f
  have hs := eLpNorm_amplitudeShellHilbert_synthesis hA hcA φ δ f (by linarith : 1 ≤ p)
    (B := ENNReal.ofReal C * (D * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
      eLpNorm f (ENNReal.ofReal p) volume) (fun η => ?_)
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  have hproj := annularProject_amplitudeInput hA hcA hχ hcχ hAχ η f
  have hthin := hd δ hδ hδone (amplitudeInput A η f)
  rw [hproj] at hthin
  calc
    _ ≤ (D * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
        eLpNorm (amplitudeInput A η f) (ENNReal.ofReal p) volume := hthin
    _ ≤ (D * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
        (ENNReal.ofReal (C * (1 + |η|) ^ (-2 : ℝ)) * eLpNorm f (ENNReal.ofReal p) volume) :=
      mul_le_mul' le_rfl ((hb η).2 f (ENNReal.ofReal p) (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)) ENNReal.ofReal_ne_top)
    _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl

end OAI.Analysis.Fourier.SquareFunction
