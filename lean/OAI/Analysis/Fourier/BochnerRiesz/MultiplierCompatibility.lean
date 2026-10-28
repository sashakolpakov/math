import OAI.Analysis.Fourier.BochnerRiesz.FourierCompatibility
import OAI.Analysis.Fourier.Wave.Multiplier

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem continuous_fourier_of_integrable {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hf)]
  exact (Real.Lp.fourierTransform _).continuous

theorem fourier_toLp_ae {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (fun ξ ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ) (hf2.toLp f)) ξ) =ᵐ[volume] 𝓕 f := by
  have hc := hf2.coeFn_toLp
  have hi : Integrable ((hf2.toLp f) : Space n → ℂ) := hf.congr hc.symm
  exact (fourierL2_coe _ hi).trans (Filter.Eventually.of_forall
    (fun ξ ↦ Real.fourier_congr_ae hc ξ))

/-- The natural-domain L² multiplier has its usual inverse-integral
representative for continuous compactly supported symbols and L¹∩L² input. -/
theorem fourierMultiplierL2_coe {n : ℕ} {m f : Space n → ℂ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f) (hf2 : MemLp f 2)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) (hf2.toLp f)) ξ) 2) :
    (fun x ↦ (OAI.Analysis.Fourier.Wave.fourierMultiplierL2 m (hf2.toLp f) hmf) x) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hmf.toLp _
  have he : (g : Space n → ℂ) =ᵐ[volume] (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
    filter_upwards [hmf.coeFn_toLp, fourier_toLp_ae hf hf2] with ξ hξ hF
    exact hξ.trans (congrArg (m ξ * ·) hF)
  have hi : Integrable (fun ξ ↦ m ξ * (𝓕 f) ξ) :=
    (hm.mul (continuous_fourier_of_integrable hf)).integrable_of_hasCompactSupport hc.mul_right
  have hg : Integrable (g : Space n → ℂ) := hi.congr he.symm
  exact (OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg).trans
    (Filter.Eventually.of_forall (fun x ↦ Real.fourierInv_congr_ae he x))

theorem frequencyHalfWave_zero_eq_fourierInv {n : ℕ} (χ : Space n → ℂ) (h : ℝ)
    (f : Space n → ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f =
      𝓕⁻ (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ)) * (𝓕 f) ξ) := by
  funext x
  unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
    one_mul, OAI.Analysis.Fourier.Wave.angularFourier_scaled]

theorem fourierMultiplierL2_coe_repr {n : ℕ} {m f : Space n → ℂ} (u : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hu : (u : Space n → ℂ) =ᵐ[volume] f)
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) u) ξ) 2) :
    (fun x ↦ (OAI.Analysis.Fourier.Wave.fourierMultiplierL2 m u hmf) x) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
  have hF := (fourierL2_coe u (hf.congr hu.symm)).trans
    (Filter.Eventually.of_forall (fun ξ ↦ Real.fourier_congr_ae hu ξ))
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hmf.toLp _
  have he : (g : Space n → ℂ) =ᵐ[volume] (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
    filter_upwards [hmf.coeFn_toLp, hF] with ξ hξ hFξ
    exact hξ.trans (congrArg (m ξ * ·) hFξ)
  have hi : Integrable (fun ξ ↦ m ξ * (𝓕 f) ξ) :=
    (hm.mul (continuous_fourier_of_integrable hf)).integrable_of_hasCompactSupport hc.mul_right
  have hg : Integrable (g : Space n → ℂ) := hi.congr he.symm
  exact (OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg).trans
    (Filter.Eventually.of_forall (fun x ↦ Real.fourierInv_congr_ae he x))

end OAI.Analysis.Fourier.BochnerRiesz
