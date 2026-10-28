import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaleyL2
import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem integral_norm_sq_of_ae_L2 {n : ℕ} (u : OAI.Analysis.Fourier.Wave.WaveL2 n) (f : Space n → ℂ)
    (he : (u : Space n → ℂ) =ᵐ[volume] f) :
    (∫ x, ‖f x‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    _ = ∫ x, ‖u x‖ ^ 2 := integral_congr_ae (he.mono
      (fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm))
    _ = _ := (OAI.Analysis.Fourier.Wave.waveL2_norm_sq_integral u).symm

theorem memLp_inverse_fourier_mul_repr {n : ℕ} {m f : Space n → ℂ} (u : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hu : (u : Space n → ℂ) =ᵐ[volume] f)
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) u) ξ) 2) :
    MemLp (𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f) ξ)) 2 :=
  (memLp_congr_ae (fourierMultiplierL2_coe_repr u hu hm hc hf hmf)).mp (Lp.memLp _)

theorem integral_norm_sq_inverse_fourier_mul_repr {n : ℕ} {m f : Space n → ℂ}
    (u : OAI.Analysis.Fourier.Wave.WaveL2 n) (hu : (u : Space n → ℂ) =ᵐ[volume] f)
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) u) ξ) 2) :
    (∫ x : Space n, ‖𝓕⁻ (fun ξ : Space n ↦ m ξ * (𝓕 f) ξ) x‖ ^ 2) =
      ‖OAI.Analysis.Fourier.Wave.fourierMultiplierL2 m u hmf‖ ^ 2 :=
  integral_norm_sq_of_ae_L2 _ _ (fourierMultiplierL2_coe_repr u hu hm hc hf hmf)

/-- Aggregate L² bound for the actual inverse-integral multipliers. -/
theorem integral_sum_norm_sq_inverse_fourier_mul_le {ι : Type*} {n : ℕ}
    (s : Finset ι) (m : ι → Space n → ℂ)
    (hm : ∀ i, Continuous (m i)) (hc : ∀ i, HasCompactSupport (m i))
    {f : Space n → ℂ} (hf : Integrable f) (u : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hu : (u : Space n → ℂ) =ᵐ[volume] f)
    (hmf : ∀ i, MemLp (fun ξ ↦ m i ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) u) ξ) 2)
    (M : ℝ) (hM : ∀ᵐ ξ ∂volume, ∑ i ∈ s, ‖m i ξ‖ ^ 2 ≤ M) :
    (∫ x, ∑ i ∈ s, ‖𝓕⁻ (fun ξ ↦ m i ξ * (𝓕 f) ξ) x‖ ^ 2) ≤
      M * ∫ x, ‖f x‖ ^ 2 := by
  have hi (i : ι) : Integrable (fun x ↦ ‖𝓕⁻ (fun ξ ↦ m i ξ * (𝓕 f) ξ) x‖ ^ 2) :=
    (memLp_inverse_fourier_mul_repr u hu (hm i) (hc i) hf (hmf i)).norm.integrable_sq
  rw [integral_finsetSum s (fun i _ ↦ hi i)]
  have he : (∑ i ∈ s, ∫ x, ‖𝓕⁻ (fun ξ ↦ m i ξ * (𝓕 f) ξ) x‖ ^ 2) =
      ∑ i ∈ s, ‖OAI.Analysis.Fourier.Wave.fourierMultiplierL2 (m i) u (hmf i)‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ ↦ integral_norm_sq_inverse_fourier_mul_repr
      u hu (hm i) (hc i) hf (hmf i))
  rw [he, integral_norm_sq_of_ae_L2 u f hu]
  exact sum_norm_sq_fourierMultiplierL2_le s m u hmf M hM

end OAI.Analysis.Fourier.BochnerRiesz
