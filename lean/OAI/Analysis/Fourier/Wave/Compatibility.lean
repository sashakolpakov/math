import OAI.Analysis.Fourier.Wave.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Wave

/-- Duality of the inverse Fourier integral against a Schwartz test function. -/
theorem inverseFourier_integral_pairing {n : ℕ} (g : Space n → ℂ)
    (hg : Integrable g) (φ : SchwartzMap (Space n) ℂ) :
    (∫ ξ, (𝓕⁻ φ) ξ * g ξ) = ∫ x, φ x * (𝓕⁻ g) x := by
  have hL : (-(innerₗ (Space n))).flip = -(innerₗ (Space n)) := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -(innerₗ (Space n)))
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar
    (by
      change Continuous (fun z : Space n × Space n ↦ -(inner ℝ z.1 z.2))
      exact continuous_inner.neg)
    φ.integrable hg
  rw [hL] at h
  have hφ (ξ : Space n) : (𝓕⁻ φ) ξ = (𝓕⁻ (φ : Space n → ℂ)) ξ :=
    congrFun (SchwartzMap.fourierInv_coe φ) ξ
  simp_rw [hφ]
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume
    (-(innerₗ (Space n))) φ ξ * g ξ) =
    ∫ x, φ x * VectorFourier.fourierIntegral Real.fourierChar volume
      (-(innerₗ (Space n))) g x
  simpa only [smul_eq_mul] using h

/-- Distributional duality identifies the inverse L² transform on test functions. -/
theorem inverseFourierL2_integral_pairing {n : ℕ} (g : WaveL2 n)
    (φ : SchwartzMap (Space n) ℂ) :
    (∫ x, φ x * ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x) =
      ∫ ξ, (𝓕⁻ φ) ξ * g ξ := by
  have h := congrArg (fun T : TemperedDistribution (Space n) ℂ ↦ T φ)
    (Lp.fourierInv_toTemperedDistribution_eq g)
  simp only [TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  change (∫ ξ, (𝓕⁻ φ) ξ * g ξ) =
    ∫ x, φ x * ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x at h
  exact h.symm

/-- For L¹ ∩ L² data, the classical inverse Fourier integral represents
the inverse unitary L² Fourier transform. -/
theorem inverseFourierL2_coe {n : ℕ} (g : WaveL2 n)
    (hg : Integrable (g : Space n → ℂ)) :
    (fun x ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x) =ᵐ[volume]
      𝓕⁻ (g : Space n → ℂ) := by
  have hc : Continuous (𝓕⁻ (g : Space n → ℂ)) := by
    rw [← Real.Lp.fourierTransformInv_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransformInv _).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro ψ hψ hsψ
  have hsc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hsψ.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ := hsc.toSchwartzMap hdiff
  have h := (inverseFourierL2_integral_pairing g φ).trans
    (inverseFourier_integral_pairing (g : Space n → ℂ) hg φ)
  simpa [φ, Complex.real_smul] using h

end OAI.Analysis.Fourier.Wave
