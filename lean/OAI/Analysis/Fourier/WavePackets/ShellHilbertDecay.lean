import OAI.Analysis.Fourier.WavePackets.ShellDecay
import OAI.Analysis.Fourier.SquareFunction.Shell.Kernel

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory FourierTransform
open scoped ContDiff

/-- Polynomial-in-width bounds for the concrete radius-Hilbert-valued
thin-shell kernel and its spatial Fréchet derivative. The spatial decay
order is arbitrary, and the reciprocal-width exponent is uniform. -/
theorem thinShellKernel_polynomial_decay {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hz : (0 : Space n) ∉ tsupport χ)
    (φ : SchwartzMap ℝ ℂ) (q : ℕ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Space n,
      ‖OAI.Analysis.Fourier.SquareFunction.thinShellKernel χ hχ.continuous φ δ x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (OAI.Analysis.Fourier.SquareFunction.thinShellKernel χ hχ.continuous φ δ) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  let b : Space n → ℂ := fun ξ => χ ((2 * Real.pi) • ξ)
  have hb : ContDiff ℝ ∞ b := by
    dsimp [b]
    fun_prop
  have hbc : HasCompactSupport b := hc.comp_smul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hbz : (0 : Space n) ∉ tsupport b := by
    intro h
    apply hz
    have ht := tsupport_comp_subset_preimage χ
      (show Continuous (fun ξ : Space n => (2 * Real.pi) • ξ) by fun_prop) h
    simpa only [Set.mem_preimage, smul_zero] using ht
  obtain ⟨Q, C, hC, hbnd⟩ := uniform_annularShell_inverse_decay hb hbc hbz φ q
  refine ⟨Q, C, hC, ?_⟩
  intro δ hδ hδone x
  have hm := OAI.Analysis.Fourier.SquareFunction.continuous_shellCutoffSymbol χ hχ.continuous φ δ
  have hmc := OAI.Analysis.Fourier.SquareFunction.hasCompactSupport_shellCutoffSymbol χ hχ.continuous hc φ δ
  have hB : 0 ≤ C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by positivity
  constructor
  · apply OAI.Analysis.Fourier.SquareFunction.norm_radiusFourierKernel_le (hm.integrable_of_hasCompactSupport hmc) x hB
    intro r
    exact (hbnd r δ hδ hδone x).1
  · apply OAI.Analysis.Fourier.SquareFunction.norm_fderiv_radiusFourierKernel_le hm hmc x hB
    intro r
    exact (hbnd r δ hδ hδone x).2

end OAI.Analysis.Fourier.WavePackets
