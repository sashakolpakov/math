import OAI.Analysis.Fourier.SquareFunction.Shell.Hilbert
import OAI.Analysis.Fourier.SquareFunction.Radius.Derivative

open OAI.Analysis.Fourier.Wave

/-! The actual annular thin-shell symbol and its Hilbert-valued kernel. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set

theorem continuous_shell_cutoff_symbol {n : ℕ} {χ : Space n → ℂ} (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Continuous (fun z : Space n × ℝ =>
      φ ((z.2 - ‖z.1‖) / δ) * χ ((2 * Real.pi) • z.1)) := by
  have hφ := φ.continuous
  fun_prop

noncomputable def shellCutoffSymbol {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) : Space n → C(RadiusInterval, ℂ) :=
  radiusCurry (fun z => φ ((z.2 - ‖z.1‖) / δ) * χ ((2 * Real.pi) • z.1))
    (continuous_shell_cutoff_symbol hχ φ δ)

@[simp] theorem shellCutoffSymbol_apply {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (ξ : Space n) (r : RadiusInterval) :
    shellCutoffSymbol χ hχ φ δ ξ r =
      φ (((r : ℝ) - ‖ξ‖) / δ) * χ ((2 * Real.pi) • ξ) := rfl

theorem continuous_shellCutoffSymbol {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) : Continuous (shellCutoffSymbol χ hχ φ δ) :=
  continuous_radiusCurry _ _

theorem hasCompactSupport_shellCutoffSymbol {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    HasCompactSupport (shellCutoffSymbol χ hχ φ δ) := by
  have hcs : HasCompactSupport (fun ξ => χ ((2 * Real.pi) • ξ)) :=
    hc.comp_smul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  apply HasCompactSupport.of_support_subset_isCompact hcs
  intro ξ hξ
  by_contra hnot
  have hz : χ ((2 * Real.pi) • ξ) = 0 := by
    by_contra hn
    exact hnot (subset_closure hn)
  apply hξ
  ext r
  simp only [shellCutoffSymbol_apply, hz, mul_zero, ContinuousMap.zero_apply]

noncomputable def thinShellKernel {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) : Space n → RadiusHilbert :=
  radiusFourierKernel (shellCutoffSymbol χ hχ φ δ)

theorem differentiable_thinShellKernel {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Differentiable ℝ (thinShellKernel χ hχ φ δ) :=
  differentiable_radiusFourierKernel (continuous_shellCutoffSymbol χ hχ φ δ)
    (hasCompactSupport_shellCutoffSymbol χ hχ hc φ δ)

theorem thinShellKernel_coe {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (x : Space n) :
    (thinShellKernel χ hχ φ δ x : RadiusInterval → ℂ) =ᵐ[radiusMeasure]
      (fun r => 𝓕⁻ (fun ξ : Space n =>
        φ (((r : ℝ) - ‖ξ‖) / δ) * χ ((2 * Real.pi) • ξ)) x) :=
  radiusFourierKernel_coe ((continuous_shellCutoffSymbol χ hχ φ δ).integrable_of_hasCompactSupport
    (hasCompactSupport_shellCutoffSymbol χ hχ hc φ δ)) x

end OAI.Analysis.Fourier.SquareFunction
