import OAI.Analysis.Fourier.SquareFunction.Shell.Dyadic
import OAI.Analysis.Fourier.SquareFunction.FourierDilation

open OAI.Analysis.Fourier.Wave

/-! Identification of the Hilbert-valued shell dilation with its actual
pointwise oscillatory integral in the radius variable. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff

noncomputable def thinShellProfile {n : ℕ} (χ : Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ a : ℝ) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) (s : ℝ) : ℂ :=
  𝓕⁻ (fun ξ : Space n => φ ((s - a⁻¹ * ‖ξ‖) / δ) *
    χ (a⁻¹ • ((2 * Real.pi) • ξ)) * 𝓕 (f : Space n → ℂ) ξ) x

theorem thinShellCycles_project_dilate {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (s : ℝ) :
    thinShellCycles φ δ
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f))
        (a • x) s = thinShellProfile χ φ δ a f x s := by
  let g := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f
  let m : Space n → ℂ := fun ξ => φ ((s - ‖ξ‖) / δ) * χ ((2 * Real.pi) • ξ)
  have he : (fun ξ : Space n => φ ((s - ‖ξ‖) / δ) *
      (𝓕 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 g)) ξ) =
        fun ξ => m ξ * 𝓕 (g : Space n → ℂ) ξ := by
    funext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.fourier_annularProject hχ hcχ (by positivity) g ξ]
    rw [SchwartzMap.fourier_coe]
    simp only [one_smul, m]
    ring
  unfold thinShellCycles
  rw [he]
  change 𝓕⁻ (fun ξ => m ξ * 𝓕 (fun y => f (a⁻¹ • y)) ξ) (a • x) = _
  rw [fourierMultiplier_dilate_cycles m f (inv_pos.mpr ha), inv_smul_smul₀ ha.ne']
  unfold thinShellProfile
  apply congrArg (fun b : Space n → ℂ => 𝓕⁻ b x)
  funext ξ
  simp only [m, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  rw [smul_comm (2 * Real.pi) a⁻¹ ξ]

theorem convolve_dilated_thinShellKernel_hilbert {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ) a) f x =
      thinShellHilbert φ δ
        (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ 1 (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f))
        (a • x) := by
  rw [convolve_dilatedKernel _ _ ha]
  exact convolve_thinShellKernel hχ hcχ φ δ
    (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate a⁻¹ (inv_ne_zero ha.ne') f) (a • x)

theorem enorm_convolve_dilated_thinShellKernel {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ) a) f x‖ₑ =
      eLpNorm (thinShellProfile χ φ δ a f x) 2 (volume.restrict (Icc (1 : ℝ) 2)) := by
  rw [convolve_dilated_thinShellKernel_hilbert hχ hcχ φ δ ha f x, enorm_thinShellHilbert]
  congr 1
  funext s
  exact thinShellCycles_project_dilate hχ hcχ φ δ ha f x s

theorem continuous_second_section {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {F : X × Y → Z} (hF : Continuous F) (x : X) :
    Continuous (fun y => F (x, y)) :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem continuous_thinShellCycles_radius_slice {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (thinShellCycles φ δ f x) :=
  continuous_second_section (continuous_thinShellCycles_joint φ δ f) x

theorem continuous_thinShellProfile_radius {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {a : ℝ} (ha : 0 < a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (thinShellProfile χ φ δ a f x) := by
  have he := funext (thinShellCycles_project_dilate hχ hcχ φ δ ha f x)
  rw [← he]
  exact continuous_thinShellCycles_radius_slice φ δ _ _

theorem dyadicThinShellSquare_eq_radius_integrals {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicThinShellSquare χ hχ.continuous φ δ f x =
      (∑' k : ℤ, ∫⁻ s in Icc (1 : ℝ) 2,
        ‖thinShellProfile χ φ δ ((2 : ℝ) ^ k) f x s‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold dyadicThinShellSquare countableSquareNorm dyadicThinShellHilbert
  congr 1
  apply tsum_congr
  intro k
  rw [enorm_convolve_dilated_thinShellKernel hχ hcχ φ δ (by positivity),
    eLpNorm_two_rpow_general _ (continuous_thinShellProfile_radius hχ hcχ φ δ
      (by positivity) f x).aestronglyMeasurable]

end OAI.Analysis.Fourier.SquareFunction
