import OAI.Analysis.Fourier.BochnerRiesz.Shell.Dilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def maximalShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ ρ : Ioi (0 : ℝ), ‖dilatedShellCycles φ Λ ρ.val f x‖ₑ

theorem measurable_shellBlockMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    {r : ℝ} (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) : Measurable (shellBlockMax φ Λ r f) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro ρ
  have hρ : 0 < ρ.val * r := mul_pos (by linarith [ρ.property.1]) hr
  have he : dilatedShellCycles φ Λ (ρ.val * r) f =
      fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ (1 / (ρ.val * r)) f x (Λ / (ρ.val * r)) :=
    funext (dilatedShellCycles_eq_thinShellCycles φ Λ hρ.ne' f)
  rw [he]
  exact (continuous_thinShellCycles_space φ (1 / (ρ.val * r)) f (Λ / (ρ.val * r))).enorm.lowerSemicontinuous

theorem maximalShellCycles_eq_iSup_blocks {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    maximalShellCycles φ Λ f x = ⨆ k : ℤ, shellBlockMax φ Λ ((2 : ℝ) ^ (-k)) f x := by
  apply le_antisymm
  · apply iSup_le
    intro ρ
    obtain ⟨j, hjlo, hjhi⟩ := exists_mem_Ico_zpow ρ.property (by norm_num : (1 : ℝ) < 2)
    have hjpos : 0 < (2 : ℝ) ^ j := by positivity
    have hq : ρ.val / (2 : ℝ) ^ j ∈ Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hjpos).mpr
        simpa only [one_mul] using hjlo
      · apply (div_le_iff₀ hjpos).mpr
        have he : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
          rw [zpow_add₀ (by norm_num), zpow_one]
          ring
        exact (hjhi.trans_eq he).le
    have he : ρ.val = (ρ.val / (2 : ℝ) ^ j) * (2 : ℝ) ^ (-(-j)) := by
      simp only [neg_neg]
      exact (div_mul_cancel₀ _ hjpos.ne').symm
    conv_lhs => rw [he]
    exact le_iSup_of_le (-j) (le_iSup_of_le ⟨ρ.val / (2 : ℝ) ^ j, hq⟩ le_rfl)
  · apply iSup_le
    intro k
    apply iSup_le
    intro ρ
    have hp : 0 < ρ.val * (2 : ℝ) ^ (-k) := mul_pos (by linarith [ρ.property.1]) (by positivity)
    exact le_iSup_of_le ⟨ρ.val * (2 : ℝ) ^ (-k), hp⟩ le_rfl

theorem measurable_maximalShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Measurable (maximalShellCycles φ Λ f) := by
  have he : maximalShellCycles φ Λ f =
      fun x ↦ ⨆ k : ℤ, shellBlockMax φ Λ ((2 : ℝ) ^ (-k)) f x :=
    funext (maximalShellCycles_eq_iSup_blocks φ Λ f)
  rw [he]
  exact Measurable.iSup (fun k ↦ measurable_shellBlockMax φ Λ (by positivity) f)

theorem shellBlockMax_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (φ : SchwartzMap ℝ ℂ) (Λ r : ℝ) (f : SchwartzMap (Space n) ℂ)
    (hcut : ∀ ρ ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
      φ (Λ - (ρ * r) * ‖ξ‖) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1) :
    shellBlockMax φ Λ r (annularProject χ h f) = shellBlockMax φ Λ r f := by
  funext x
  unfold shellBlockMax
  apply iSup_congr
  intro ρ
  rw [dilatedShellCycles_annularProject hχ hc hh φ Λ (ρ.val * r) f (hcut ρ.val ρ.property)]

end OAI.Analysis.Fourier.BochnerRiesz
