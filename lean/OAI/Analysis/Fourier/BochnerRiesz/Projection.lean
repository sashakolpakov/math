import OAI.Analysis.Fourier.BochnerRiesz.Shell.Bound
import Mathlib.Analysis.Distribution.FourierMultiplier

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- A smooth annular cutoff, applied in the manuscript's angular-frequency convention. -/
def annularProject {n : ℕ} (χ : Space n → ℂ) (h : ℝ) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ))) f

theorem annularProject_symbol_temperate {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h) :
    Function.HasTemperateGrowth (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ))) := by
  have hs : HasCompactSupport (fun ξ ↦ χ ((h * (2 * Real.pi)) • ξ)) :=
    hc.comp_smul (mul_ne_zero hh.ne' (by positivity))
  have hd : ContDiff ℝ ∞ (fun ξ ↦ χ ((h * (2 * Real.pi)) • ξ)) :=
    hχ.comp (by fun_prop)
  simpa only [smul_smul] using hs.hasTemperateGrowth hd

theorem fourier_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    (𝓕 (annularProject χ h f) : SchwartzMap (Space n) ℂ) ξ =
      χ (h • ((2 * Real.pi) • ξ)) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ := by
  rw [annularProject, SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (annularProject_symbol_temperate hχ hc hh)]
  rfl

theorem angularFourier_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (annularProject χ h f) ξ = χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
  conv_lhs => rw [← he]
  rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  change (𝓕 (annularProject χ h f) : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [fourier_annularProject hχ hc hh f, he]
  congr 1
  rw [SchwartzMap.fourier_coe, ← OAI.Analysis.Fourier.Wave.angularFourier_scaled, he]

theorem annularProject_eq_frequencyHalfWave {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    annularProject χ h f x = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f x := by
  rw [annularProject, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  rw [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [SchwartzMap.smulLeftCLM_apply_apply (annularProject_symbol_temperate hχ hc hh)]
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      OAI.Analysis.Fourier.Wave.angularFourier_scaled, smul_eq_mul, SchwartzMap.fourier_coe]

theorem eLpNorm_annularProject_le {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (annularProject χ h f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume * eLpNorm f p volume := by
  have he : (annularProject χ h f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f :=
    funext (annularProject_eq_frequencyHalfWave hχ hc hh f)
  rw [he]
  exact eLpNorm_frequencyHalfWave_zero_le hχ.continuous hc hh f.integrable hp hptop

theorem integrable_angularInverse_cutoff {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let g : SchwartzMap (Space n) ℂ := schwartzDilate (2 * Real.pi) hp (hc.toSchwartzMap hχ)
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ = (𝓕⁻ g : SchwartzMap (Space n) ℂ) := by
    funext x
    rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled, SchwartzMap.fourierInv_coe]
    rfl
  rw [he]
  exact (𝓕⁻ g : SchwartzMap (Space n) ℂ).integrable

theorem annularProject_uniform_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 < A ∧ ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (annularProject χ h f) p volume ≤ ENNReal.ofReal A * eLpNorm f p volume := by
  let D := eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume
  have hD : D ≠ ⊤ := (memLp_one_iff_integrable.mpr (integrable_angularInverse_cutoff hχ hc)).eLpNorm_ne_top
  have hd : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨D.toReal + 1, by positivity, ?_⟩
  intro h hh f p hp hptop
  exact (eLpNorm_annularProject_le hχ hc hh f hp hptop).trans (mul_le_mul' hd le_rfl)

theorem annularProject_support_cutoff {n : ℕ} {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (hψ : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1) :
    ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (annularProject χ h f) ξ ≠ 0 → ψ (h • ξ) = 1 := by
  intro ξ hξ
  rw [angularFourier_annularProject hχ hc hh f] at hξ
  exact hψ (h • ξ) (mul_ne_zero_iff.mp hξ).1

theorem thinShellCycles_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (φ : ℝ → ℂ) (δ s : ℝ) (f : SchwartzMap (Space n) ℂ)
    (hcut : ∀ ξ : Space n, φ ((s - ‖ξ‖) / δ) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1)
    (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ (annularProject χ h f) x s = OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x s := by
  unfold OAI.Analysis.Fourier.SquareFunction.thinShellCycles
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    dsimp only
    rw [fourier_annularProject hχ hc hh f]
    by_cases hz : φ ((s - ‖ξ‖) / δ) = 0
    · simp only [hz, zero_mul]
    · rw [hcut ξ hz, one_mul]

end OAI.Analysis.Fourier.BochnerRiesz
