import OAI.Analysis.Fourier.BesselPotential.Schwartz
import OAI.Analysis.Fourier.BochnerRiesz.Annular
import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory
open scoped ContDiff ENNReal

namespace OAI.Analysis.Fourier.BesselPotential

/-- Exact cancellation of the normalized inverse Bessel symbol on an annulus. -/
theorem inverse_annular_bessel_symbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    (h^σ : ℝ) • (OAI.Analysis.Fourier.BochnerRiesz.annularSobolevSymbol χ (-σ) (h,h • ξ) *
      (((1+‖ξ‖^2)^(σ/2) : ℝ) • (1 : ℂ))) = χ (h • ξ) := by
  have hbase : 0 < 1+‖ξ‖^2 := by positivity
  have h₁ : (h^σ : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hh σ).ne'
  have h₂ : ((1+‖ξ‖^2)^(σ/2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hbase _).ne'
  rw [OAI.Analysis.Fourier.BochnerRiesz.annularSobolevSymbol_scaling χ (-σ) hh]
  rw [Real.rpow_neg hh.le,show -σ/2 = -(σ/2) by ring,Real.rpow_neg hbase.le]
  simp only [Complex.real_smul,Complex.ofReal_inv,mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr h₁,Complex.ofReal_ne_zero.mpr h₂]

/-- Applying an annular cutoff to the input is the normalized inverse
Bessel multiplier applied to its actual Bessel potential. -/
theorem frequencyHalfWave_eq_inverse_bessel {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f x = h^σ •
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ => OAI.Analysis.Fourier.BochnerRiesz.annularSobolevSymbol χ (-σ) (h,ξ))
        h 0 (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave,zero_mul,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_mul]
  rw [← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real]
  congr 1
  funext ξ
  rw [angularFourier_besselPotential]
  have hc := inverse_annular_bessel_symbol χ σ hh ξ
  simp only [Complex.real_smul,mul_one] at hc ⊢
  calc
    χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ =
      ((h^σ : ℝ) : ℂ) * (OAI.Analysis.Fourier.BochnerRiesz.annularSobolevSymbol χ (-σ) (h,h • ξ) *
        (((1+‖ξ‖^2)^(σ/2) : ℝ) : ℂ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by rw [hc]
    _ = _ := by ring

/-- The annular inverse estimate, uniform in the scale and in the finite
Lp exponent. The cutoff need not equal one anywhere. -/
theorem annularProject_inverse_bessel_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hzero : (0 : Space n) ∉ tsupport χ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) p volume ≤
        ENNReal.ofReal (C*h^σ) * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) p volume := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound isCompact_Icc hc
    (OAI.Analysis.Fourier.BochnerRiesz.contDiff_annularSobolevSymbol hχ hzero (-σ))
    (OAI.Analysis.Fourier.BochnerRiesz.tsupport_annularSobolevSymbol χ (-σ))
  refine ⟨C,hC,?_⟩
  intro h hh hone f p hp hptop
  have hint : Integrable (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) := by
    rw [← besselPotentialSchwartz_eq]
    exact (besselPotentialSchwartz σ f).integrable
  have heq : (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f : Space n → ℂ) = h^σ •
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ => OAI.Analysis.Fourier.BochnerRiesz.annularSobolevSymbol χ (-σ) (h,ξ))
        h 0 (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) := by
    funext x
    rw [OAI.Analysis.Fourier.BochnerRiesz.annularProject_eq_frequencyHalfWave hχ hc hh]
    exact frequencyHalfWave_eq_inverse_bessel χ σ hh f x
  rw [heq,eLpNorm_const_smul,Real.enorm_eq_ofReal (Real.rpow_nonneg hh.le _)]
  calc
    _ ≤ ENNReal.ofReal (h^σ) * (ENNReal.ofReal C *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) p volume) :=
      mul_le_mul' le_rfl (hbound h ⟨hh.le,hone⟩ h hh _ hint p hp hptop)
    _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl

end OAI.Analysis.Fourier.BesselPotential
