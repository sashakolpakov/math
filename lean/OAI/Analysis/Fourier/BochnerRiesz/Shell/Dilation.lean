import OAI.Analysis.Fourier.BochnerRiesz.FixedLocalMaximal
import OAI.Analysis.Fourier.BochnerRiesz.ProjectionDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem dilatedShellCycles_eq_frequencyHalfWave {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (Λ ρ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dilatedShellCycles φ Λ ρ f x =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ : Space n ↦ φ (Λ - ρ / (2 * Real.pi) * ‖ξ‖)) 1 0 f x := by
  rw [frequencyHalfWave_zero_eq_fourierInv]
  unfold dilatedShellCycles
  apply Real.fourierInv_congr_ae
  filter_upwards [] with ξ
  simp only [one_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), SchwartzMap.fourier_coe]
  congr 1
  congr 1
  field_simp

theorem dilatedShellCycles_schwartzDilate {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (Λ ρ : ℝ) {r : ℝ} (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dilatedShellCycles φ Λ ρ (schwartzDilate r hr.ne' f) x =
      dilatedShellCycles φ Λ (ρ * r) f (r • x) := by
  rw [dilatedShellCycles_eq_frequencyHalfWave, dilatedShellCycles_eq_frequencyHalfWave]
  change OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave _ 1 0 (fun y ↦ f (r • y)) x = _
  rw [frequencyHalfWave_zero_dilate _ _ _ hr, one_mul]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, one_smul]
  apply congrArg (fun g : Space n → ℂ ↦ OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (r • x))
  funext ξ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  congr 1
  congr 1
  ring

def shellBlockMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ r : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ ρ : Icc (1 : ℝ) 2, ‖dilatedShellCycles φ Λ (ρ.val * r) f x‖ₑ

theorem dyadicShellMax_schwartzDilate {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (Λ : ℝ) {r : ℝ} (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicShellMax φ Λ (schwartzDilate r hr.ne' f) x = shellBlockMax φ Λ r f (r • x) := by
  unfold dyadicShellMax shellBlockMax
  apply iSup_congr
  intro ρ
  rw [dilatedShellCycles_schwartzDilate φ Λ ρ.val hr]

theorem eLpNorm_shellBlockMax_bound {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    {p B : ℝ≥0∞}
    (hlocal : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (dyadicShellMax φ Λ g) p volume ≤ B * eLpNorm g p volume)
    {r : ℝ} (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (shellBlockMax φ Λ r f) p volume ≤ B * eLpNorm f p volume := by
  have H := hlocal (schwartzDilate r hr.ne' f)
  have he : dyadicShellMax φ Λ (schwartzDilate r hr.ne' f) =
      fun x ↦ shellBlockMax φ Λ r f (r • x) := funext (dyadicShellMax_schwartzDilate φ Λ hr f)
  rw [he, eLpNorm_dilate_enormed (shellBlockMax φ Λ r f) p hr, eLpNorm_schwartzDilate f p hr] at H
  let D : ℝ≥0∞ := ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal)
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hDtop : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have H' : D * eLpNorm (shellBlockMax φ Λ r f) p volume ≤ D * (B * eLpNorm f p volume) := by
    simpa only [D, mul_left_comm, mul_assoc] using H
  have HH := mul_le_mul' (le_refl D⁻¹) H'
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul] using HH

end OAI.Analysis.Fourier.BochnerRiesz
