import OAI.Analysis.PDE.WaveEquation.HighEstimate
import OAI.Analysis.Fourier.WavePackets.WaveDataLowTime
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem halfWave_cosine_scalar (a : ℝ) :
    (1/2:ℝ) • (Complex.exp (-Complex.I * (a:ℂ)) +
      Complex.exp (-Complex.I * ((-a:ℝ):ℂ))) = (Real.cos a : ℂ) := by
  have h₁ : -Complex.I * (a:ℂ) = ((-a:ℝ):ℂ) * Complex.I := by push_cast; ring
  have h₂ : -Complex.I * ((-a:ℝ):ℂ) = (a:ℂ) * Complex.I := by push_cast; ring
  rw [h₁,h₂,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

theorem halfWave_sine_scalar (a : ℝ) :
    Complex.I * ((1/2:ℝ) • (Complex.exp (-Complex.I * (a:ℂ)) -
      Complex.exp (-Complex.I * ((-a:ℝ):ℂ)))) = (Real.sin a : ℂ) := by
  have h₁ : -Complex.I * (a:ℂ) = ((-a:ℝ):ℂ) * Complex.I := by push_cast; ring
  have h₂ : -Complex.I * ((-a:ℝ):ℂ) = (a:ℂ) * Complex.I := by push_cast; ring
  rw [h₁,h₂,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem integral_cosine_unit (a : ℝ) :
    (∫ s in Icc (0:ℝ) 1, (Real.cos (a*s) : ℂ)) = (Real.sinc a : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  by_cases ha : a = 0
  · subst a
    simp
  · have h := integral_cos_mul_complex (Complex.ofReal_ne_zero.mpr ha) (0:ℝ) 1
    simpa only [Complex.ofReal_mul, Complex.ofReal_cos, mul_one, Complex.ofReal_zero,
      mul_zero, Complex.sin_zero, zero_div, sub_zero, Real.sinc_of_ne_zero ha,
      Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_one] using h

theorem frequencyCosine_eq_inverse {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    (1/2:ℝ) • (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 t f x + OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-t) f x) =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.cos (t*‖ξ‖) : ℂ) * χ ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hχ.continuous
  have hi (s : ℝ) := OAI.Analysis.Fourier.LocalSmoothing.integrable_wave_cutoff_symbol hχ.continuous hC 1 s f
  have hadd := congrFun (OAI.Analysis.Fourier.WavePackets.angularInverse_add_integrable (hi t) (hi (-t))) x
  change OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x = OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x + OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x at hadd
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave]
  rw [← hadd, ← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real]
  congr 1
  funext ξ
  simp only [Pi.add_apply,one_smul,neg_mul]
  calc
    _ = ((1/2:ℝ) • (Complex.exp (-Complex.I * (t*‖ξ‖:ℝ)) +
        Complex.exp (-Complex.I * (-(t*‖ξ‖):ℝ)))) * χ ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
      simp only [Complex.real_smul]
      ring_nf
    _ = _ := by rw [halfWave_cosine_scalar]

end OAI.Analysis.PDE.WaveEquation
