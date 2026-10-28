import OAI.Analysis.Fourier.WavePackets.ShellAmplitudeDecay
import OAI.Analysis.Fourier.SquareFunction.Amplitude.Kernel

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory FourierTransform
open scoped ContDiff

/-- Uniform polynomial width loss and arbitrary spatial decay for a smooth
compact radius-dependent shell amplitude supported away from zero frequency. -/
theorem amplitudeShellKernel_polynomial_decay {n : ℕ} {A : ℝ × Space n → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : Space n)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (q : ℕ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Space n,
      ‖OAI.Analysis.Fourier.SquareFunction.amplitudeShellKernel A ha.continuous φ δ x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (OAI.Analysis.Fourier.SquareFunction.amplitudeShellKernel A ha.continuous φ δ) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  obtain ⟨Q, C, hC, hbnd⟩ := uniform_amplitudeShell_inverse_decay ha hc hz φ q
  refine ⟨Q, C, hC, ?_⟩
  intro δ hδ hδone x
  have hm := OAI.Analysis.Fourier.SquareFunction.continuous_amplitudeShellSymbol A ha.continuous φ δ
  have hmc := OAI.Analysis.Fourier.SquareFunction.hasCompactSupport_amplitudeShellSymbol A ha.continuous hc φ δ
  have hB : 0 ≤ C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by positivity
  constructor
  · apply OAI.Analysis.Fourier.SquareFunction.norm_radiusFourierKernel_le (hm.integrable_of_hasCompactSupport hmc) x hB
    intro r
    exact (hbnd r δ hδ hδone x).1
  · apply OAI.Analysis.Fourier.SquareFunction.norm_fderiv_radiusFourierKernel_le hm hmc x hB
    intro r
    exact (hbnd r δ hδ hδone x).2

end OAI.Analysis.Fourier.WavePackets
