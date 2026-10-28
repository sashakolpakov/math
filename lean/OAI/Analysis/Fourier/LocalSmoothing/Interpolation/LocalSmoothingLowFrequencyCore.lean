import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Young
import OAI.Analysis.Fourier.BesselPotential.Schwartz

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

def unweightedCutoff {n : ℕ} (χ : Space n → ℂ) (m : Space n → ℝ) (ξ : Space n) : ℂ :=
  (m ξ)⁻¹ • χ ξ

theorem contDiff_unweightedCutoff {n : ℕ} {χ : Space n → ℂ} {m : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0) :
    ContDiff ℝ ∞ (unweightedCutoff χ m) := by
  exact (hm.1.inv hne).smul hχ

theorem hasCompactSupport_unweightedCutoff {n : ℕ} {χ : Space n → ℂ} (m : Space n → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (unweightedCutoff χ m) := by
  simpa only [unweightedCutoff, Pi.smul_apply] using!
    (hχ.smul_left (f := fun ξ : Space n => (m ξ)⁻¹))

theorem frequencyHalfWave_unweight {n : ℕ} (χ : Space n → ℂ) {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (unweightedCutoff χ m) 1 t (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f) =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 t f := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  congr 1
  funext ξ
  rw [OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hm]
  simp only [one_smul, unweightedCutoff, Complex.real_smul, Complex.ofReal_inv]
  have hc : (m ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne ξ)
  field_simp

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
