import OAI.Analysis.Fourier.SquareFunction.Shell.Convolution
import OAI.Analysis.Fourier.SquareFunction.ConvolutionDensity

open OAI.Analysis.Fourier.Wave

/-! Operator bounds for the actual Hilbert-valued shell convolution kernel. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff

theorem norm_radiusFourierKernel_le_integral {n : ℕ}
    (m : Space n → C(RadiusInterval, ℂ)) (x : Space n) :
    ‖radiusFourierKernel m x‖ ≤ ∫ ξ, ‖m ξ‖ := by
  apply (norm_radiusToL2_le _).trans
  rw [fourierInv_eq_spatialPhase_smul]
  simpa only [norm_smul, norm_spatialPhase, one_mul] using
    norm_integral_le_integral_norm (fun ξ => spatialPhase x ξ • m ξ)

theorem bddAbove_norm_thinShellKernel {n : ℕ} (χ : Space n → ℂ) (hχ : Continuous χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    BddAbove (range fun x => ‖thinShellKernel χ hχ φ δ x‖) := by
  refine ⟨∫ ξ, ‖shellCutoffSymbol χ hχ φ δ ξ‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_radiusFourierKernel_le_integral _ x

theorem thinShellKernel_two_schwartz {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) f) 2 volume ≤
      (ENNReal.ofReal δ ^ (1 / 2 : ℝ) *
        (eLpNorm φ 2 volume * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume)) * eLpNorm f 2 volume := by
  rw [funext (convolve_thinShellKernel hχ hcχ φ δ f)]
  calc
    _ ≤ ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume *
        eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) 2 volume :=
      thinShellHilbert_two_bound φ hδ _
    _ ≤ ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume *
        (eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume * eLpNorm f 2 volume) :=
      mul_le_mul' le_rfl (OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_annularProject_le hχ hcχ
        (by positivity) f (by norm_num) (by norm_num))
    _ = _ := by ring

theorem thinShellKernel_two_integrable {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hKi : Integrable (thinShellKernel χ hχ.continuous φ δ))
    {f : Space n → ℂ} (hfi : Integrable f) (hfp : MemLp f 2 volume) :
    eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) f) 2 volume ≤
      (ENNReal.ofReal δ ^ (1 / 2 : ℝ) *
        (eLpNorm φ 2 volume * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume)) * eLpNorm f 2 volume := by
  have hC : (ENNReal.ofReal δ ^ (1 / 2 : ℝ) *
        (eLpNorm φ 2 volume * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
    · exact ENNReal.mul_ne_top (φ.memLp 2).ne
        (memLp_one_iff_integrable.mpr (OAI.Analysis.Fourier.BochnerRiesz.integrable_angularInverse_cutoff hχ hcχ)).ne
  exact convolution_bound_of_schwartz_ae
    (differentiable_thinShellKernel χ hχ.continuous hcχ φ δ).continuous hKi
    (bddAbove_norm_thinShellKernel χ hχ.continuous φ δ) (by norm_num) (by norm_num) hC
    (thinShellKernel_two_schwartz hχ hcχ φ hδ) hfi hfp

theorem localSmoothing_thinShellKernel_schwartz (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ) (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) f)
        (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_projected_thinShellHilbert hls hn hχ hcχ hψ hcψ
    hzero hcut φ hp hε
  refine ⟨C, hC, fun δ hδ hδone f => ?_⟩
  have he := funext (convolve_thinShellKernel hχ hcχ φ δ f)
  rw [he]
  exact hb δ hδ hδone f

theorem localSmoothing_thinShellKernel_integrable (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ) (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Integrable (thinShellKernel χ hχ.continuous φ δ) →
      ∀ f : Space n → ℂ, Integrable f → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) f)
        (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_thinShellKernel_schwartz hls hn hχ hcχ hψ hcψ
    hzero hcut φ hp hε
  refine ⟨C, hC, fun δ hδ hδone hKi f hfi hfp => ?_⟩
  apply convolution_bound_of_schwartz_ae
    (differentiable_thinShellKernel χ hχ.continuous hcχ φ δ).continuous hKi
    (bddAbove_norm_thinShellKernel χ hχ.continuous φ δ)
    (by simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)) ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hb δ hδ hδone) hfi hfp

end OAI.Analysis.Fourier.SquareFunction
