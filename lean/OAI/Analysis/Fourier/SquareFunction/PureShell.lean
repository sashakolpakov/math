import OAI.Analysis.Fourier.SquareFunction.Shell.Profile
import OAI.Analysis.Fourier.SquareFunction.Cutoff

open OAI.Analysis.Fourier.Wave

/-! The all-dyadic estimate for a compactly supported pure thin shell,
with the auxiliary annular cutoffs removed from the final operator. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff

noncomputable def pureThinShellProfile {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ a : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (s : ℝ) : ℂ :=
  𝓕⁻ (fun ξ : Space n => φ ((s - a⁻¹ * ‖ξ‖) / δ) * 𝓕 (f : Space n → ℂ) ξ) x

noncomputable def pureThinShellSquare {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  (∑' k : ℤ, ∫⁻ s in Icc (1 : ℝ) 2,
    ‖pureThinShellProfile φ δ ((2 : ℝ) ^ k) f x s‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

theorem thinShellProfile_eq_pure {n : ℕ} {χ : Space n → ℂ}
    (hχ : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 3 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ u : ℝ, φ u ≠ 0 → |u| ≤ 2)
    {δ a s : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4) (ha : 0 < a)
    (hs : s ∈ Icc (1 : ℝ) 2) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    thinShellProfile χ φ δ a f x s = pureThinShellProfile φ δ a f x s := by
  unfold thinShellProfile pureThinShellProfile
  apply congrArg (fun m : Space n → ℂ => 𝓕⁻ m x)
  funext ξ
  by_cases hz : φ ((s - a⁻¹ * ‖ξ‖) / δ) = 0
  · simp [hz]
  · have hu := abs_le.mp (hφ _ hz)
    have hlo := (le_div_iff₀ hδ).mp hu.1
    have hhi := (div_le_iff₀ hδ).mp hu.2
    have hηlo : 1 / 2 ≤ ‖a⁻¹ • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      linarith [hs.1]
    have hηhi : ‖a⁻¹ • ξ‖ ≤ 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      linarith [hs.2]
    have hc := hχ (a⁻¹ • ξ) hηlo hηhi
    rw [smul_comm (2 * Real.pi) a⁻¹ ξ] at hc
    rw [hc, mul_one]

theorem dyadicThinShellSquare_eq_pure {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 3 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ u : ℝ, φ u ≠ 0 → |u| ≤ 2)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicThinShellSquare χ hχ.continuous φ δ f x = pureThinShellSquare φ δ f x := by
  rw [dyadicThinShellSquare_eq_radius_integrals hχ hcχ]
  unfold pureThinShellSquare
  congr 1
  apply tsum_congr
  intro k
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only
  rw [thinShellProfile_eq_pure hχone φ hφ hδ hδsmall (by positivity) hs]

theorem localSmoothing_pureThinShellSquare (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ u : ℝ, φ u ≠ 0 → |u| ≤ 2)
    {p ε : ℝ} (hp : 2 < p) (hε : 0 < ε) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (pureThinShellSquare φ δ f) (ENNReal.ofReal p) volume ≤
        D * ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) *
          ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
            eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨χ, ψ, hχ, hcχ, hzχ, hψ, hcψ, hzψ, hχone, hcut, hband⟩ := exists_stein_annular_cutoffs n
  obtain ⟨D, hD, hbound⟩ := localSmoothing_dyadicThinShellSquare hls hn hχ hcχ hzχ
    hψ hcψ hzψ hcut hband φ hp hε
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδsmall f
  have he := funext (dyadicThinShellSquare_eq_pure hχ hcχ hχone φ hφ hδ hδsmall f)
  rw [← he]
  exact hbound δ hδ (by linarith) f

end OAI.Analysis.Fourier.SquareFunction
