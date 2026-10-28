import OAI.Analysis.Fourier.SquareFunction.Shell.Kernel
import OAI.Analysis.Fourier.SquareFunction.VectorConvolution

open OAI.Analysis.Fourier.Wave

/-! The annular shell operator is convolution with its concrete
`L²([1,2])`-valued inverse-Fourier kernel. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ContDiff

theorem integrable_continuous_smul_compact {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : Space n → ℂ} {m : Space n → E} (ha : Continuous a)
    (hm : Continuous m) (hc : HasCompactSupport m) :
    Integrable (fun ξ => a ξ • m ξ) :=
  (ha.smul hm).integrable_of_hasCompactSupport hc.smul_left

theorem convolve_radiusFourierKernel {n : ℕ}
    {m : Space n → C(RadiusInterval, ℂ)} {f : Space n → ℂ}
    (hm : Integrable m) (hf : Integrable f) (x : Space n) :
    convolveKernel (radiusFourierKernel m) f x =
      radiusToL2 (𝓕⁻ (fun ξ => 𝓕 f ξ • m ξ) x) := by
  obtain ⟨hint, heq⟩ := inverseFourier_smul_eq_convolve hm hf x
  rw [heq]
  unfold convolveKernel radiusFourierKernel
  simp_rw [← radiusToL2.map_smul]
  exact radiusToL2.integral_comp_comm hint

theorem fourier_shellCutoffSymbol_project {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    𝓕⁻ (fun ξ => 𝓕 (f : Space n → ℂ) ξ • shellCutoffSymbol χ hχ.continuous φ δ ξ) x =
      thinShellRadiusMap φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) x := by
  have hm : Integrable (fun ξ =>
      𝓕 (f : Space n → ℂ) ξ • shellCutoffSymbol χ hχ.continuous φ δ ξ) := by
    apply integrable_continuous_smul_compact
      (m := shellCutoffSymbol χ hχ.continuous φ δ)
    · exact (𝓕 f).continuous
    · exact continuous_shellCutoffSymbol χ hχ.continuous φ δ
    · exact hasCompactSupport_shellCutoffSymbol χ hχ.continuous hc φ δ
  ext r
  rw [fourierInv_continuousMap_apply hm x r]
  change 𝓕⁻ (fun ξ => 𝓕 (f : Space n → ℂ) ξ * shellCutoffSymbol χ hχ.continuous φ δ ξ r) x =
    thinShellCycles φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) x r
  unfold thinShellCycles
  apply congrArg (fun a : Space n → ℂ => 𝓕⁻ a x)
  funext ξ
  rw [shellCutoffSymbol_apply, OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hc (by positivity) f ξ]
  rw [← SchwartzMap.fourier_coe]
  simp only [one_smul]
  ring

theorem convolve_thinShellKernel {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (thinShellKernel χ hχ.continuous φ δ) f x =
      thinShellHilbert φ δ (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 f) x := by
  unfold thinShellKernel
  rw [convolve_radiusFourierKernel
    ((continuous_shellCutoffSymbol χ hχ.continuous φ δ).integrable_of_hasCompactSupport
      (hasCompactSupport_shellCutoffSymbol χ hχ.continuous hc φ δ)) f.integrable x,
    fourier_shellCutoffSymbol_project hχ hc φ δ f x]
  rfl

end OAI.Analysis.Fourier.SquareFunction
