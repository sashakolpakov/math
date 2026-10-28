import OAI.Analysis.Fourier.Wave.AngularTransform
import Mathlib.Analysis.Distribution.FourierMultiplier

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped ContDiff ENNReal

namespace OAI.Analysis.Fourier.BesselPotential

/-- A Schwartz Fourier multiplier written with the manuscript's angular
frequencies. Its coercion is the actual inverse integral when the symbol
has temperate growth. -/
def angularSchwartzMultiplier {n : ℕ} (m : Space n → ℝ)
    (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ => m ((2*Real.pi) • ξ)) f

theorem angularSchwartzMultiplier_temperate {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) :
    (fun ξ => m ((2*Real.pi) • ξ)).HasTemperateGrowth :=
  hm.comp (by fun_prop)

theorem angularSchwartzMultiplier_eq_integral {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    angularSchwartzMultiplier m f x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => m ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x := by
  rw [angularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe,OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (angularSchwartzMultiplier_temperate hm)]
    dsimp only
    rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled,SchwartzMap.fourier_coe]

theorem angularFourier_angularSchwartzMultiplier {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (angularSchwartzMultiplier m f) ξ = m ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  have hp : (2*Real.pi : ℝ) ≠ 0 := by positivity
  have he : (2*Real.pi) • ((2*Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul,mul_inv_cancel₀ hp,one_smul]
  conv_lhs => rw [← he]
  rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  change (𝓕 (angularSchwartzMultiplier m f) : SchwartzMap (Space n) ℂ)
    ((2*Real.pi)⁻¹ • ξ) = _
  rw [angularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (angularSchwartzMultiplier_temperate hm),he]
  congr 1
  rw [SchwartzMap.fourier_coe,← OAI.Analysis.Fourier.Wave.angularFourier_scaled,he]

def besselPotentialSchwartz {n : ℕ} (s : ℝ) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  angularSchwartzMultiplier (fun ξ => (1+‖ξ‖^2)^(s/2)) f

theorem besselPotentialSchwartz_eq {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    (besselPotentialSchwartz s f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f := by
  funext x
  exact angularSchwartzMultiplier_eq_integral
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (s/2)) f x

theorem angularFourier_besselPotential {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) ξ =
      ((1+‖ξ‖^2)^(s/2) : ℝ) • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  rw [← besselPotentialSchwartz_eq]
  exact angularFourier_angularSchwartzMultiplier
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (s/2)) f ξ

theorem memLp_besselPotential {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    MemLp (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) p volume := by
  rw [← besselPotentialSchwartz_eq]
  exact (besselPotentialSchwartz s f).memLp p

end OAI.Analysis.Fourier.BesselPotential
