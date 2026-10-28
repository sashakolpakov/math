import OAI.Analysis.Fourier.SquareFunction.Amplitude.Bounds
import OAI.Analysis.Fourier.SquareFunction.Shell.OperatorBounds

open OAI.Analysis.Fourier.Wave

/-! Extension of the amplitude-shell estimates from Schwartz functions to
the full integrable `Lp` domain of the actual convolution. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

theorem bddAbove_norm_amplitudeShellKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    BddAbove (range fun x => ‖amplitudeShellKernel A hA φ δ x‖) := by
  refine ⟨∫ ξ, ‖amplitudeShellSymbol A hA φ δ ξ‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_radiusFourierKernel_le_integral _ x

theorem amplitudeShellKernel_two_integrable {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ →
      Integrable (amplitudeShellKernel A hA.continuous φ δ) →
      ∀ f : Space n → ℂ, Integrable f → MemLp f 2 volume →
      eLpNorm (convolveKernel (amplitudeShellKernel A hA.continuous φ δ) f) 2 volume ≤
        (ENNReal.ofReal δ ^ (1 / 2 : ℝ) * C) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hb⟩ := amplitudeShellHilbert_two_bound hA hcA φ
  refine ⟨C, hC, fun δ hδ hKi f hfi hfp => ?_⟩
  apply convolution_bound_of_schwartz_ae
    (differentiable_amplitudeShellKernel A hA.continuous hcA φ δ).continuous hKi
    (bddAbove_norm_amplitudeShellKernel A hA.continuous φ δ)
    (by norm_num) (by norm_num)
    (ENNReal.mul_ne_top
      ((ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne) hC)
    ?_ hfi hfp
  intro g
  rw [funext (convolve_amplitudeShellKernel A hA.continuous hcA φ δ g)]
  exact hb δ hδ g

theorem localSmoothing_amplitudeShellKernel_integrable (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    {χ ψ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzψ : (0 : Space n) ∉ tsupport ψ)
    (hχψ : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (hAχ : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Integrable (amplitudeShellKernel A hA.continuous φ δ) →
      ∀ f : Space n → ℂ, Integrable f → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (convolveKernel (amplitudeShellKernel A hA.continuous φ δ) f)
        (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_amplitudeShellHilbert hls hn hA hcA hχ hcχ
    hψ hcψ hzψ hχψ hAχ φ hp hε
  refine ⟨C, hC, fun δ hδ hδone hKi f hfi hfp => ?_⟩
  apply convolution_bound_of_schwartz_ae
    (differentiable_amplitudeShellKernel A hA.continuous hcA φ δ).continuous hKi
    (bddAbove_norm_amplitudeShellKernel A hA.continuous φ δ)
    (by simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) ?_ hfi hfp
  intro g
  rw [funext (convolve_amplitudeShellKernel A hA.continuous hcA φ δ g)]
  exact hb δ hδ hδone g

end OAI.Analysis.Fourier.SquareFunction
