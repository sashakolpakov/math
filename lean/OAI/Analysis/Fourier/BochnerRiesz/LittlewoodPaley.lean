import OAI.Analysis.Fourier.BochnerRiesz.DyadicOverlap
import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaleyIntegral

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def dyadicAnnularKernel {n : ℕ} (χ : Space n → ℂ) (k : ℤ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ χ ((2 : ℝ) ^ (-k) • ξ))

def dyadicAnnularConvolution {n : ℕ} (χ : Space n → ℂ) (k : ℤ)
    (f : Space n → ℂ) : Space n → ℂ :=
  OAI.Analysis.Fourier.WavePackets.complexConvolution (dyadicAnnularKernel χ k) f volume

theorem dyadicAnnularConvolution_eq_fourierInv {n : ℕ} {χ f : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hf : Integrable f) (k : ℤ) :
    dyadicAnnularConvolution χ k f =
      𝓕⁻ (fun ξ ↦ χ ((2 : ℝ) ^ (-k) • ((2 * Real.pi) • ξ)) * (𝓕 f) ξ) := by
  funext x
  unfold dyadicAnnularConvolution dyadicAnnularKernel
  rw [← frequencyHalfWave_zero_eq_convolution hχ hc (zpow_pos (by norm_num) _) hf x]
  exact congrFun (frequencyHalfWave_zero_eq_fourierInv χ _ f) x

/-- The finite dyadic square-sum estimate for the actual convolution kernels.
It holds for arbitrary L¹∩L² input, including sharply truncated functions.
The constant is independent of the finite set of scales. -/
theorem dyadicAnnularConvolution_L2 {n N : ℕ} {χ f : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ ξ, ‖χ ξ‖ ≤ M)
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (∀ k : ℤ, MemLp (dyadicAnnularConvolution χ k f) 2) ∧
    ∀ s : Finset ℤ,
      (∫ x, ∑ k ∈ s, ‖dyadicAnnularConvolution χ k f x‖ ^ 2) ≤
        ((2 * (N : ℝ) + 1) * M ^ 2) * ∫ x, ‖f x‖ ^ 2 := by
  let m : ℤ → Space n → ℂ := fun k ξ ↦ χ ((2 : ℝ) ^ (-k) • ((2 * Real.pi) • ξ))
  have hm (k : ℤ) : Continuous (m k) := by
    dsimp only [m]
    fun_prop
  have hcm (k : ℤ) : HasCompactSupport (m k) :=
    (hc.comp_smul (ne_of_gt (zpow_pos (by norm_num) (-k)))).comp_smul (by positivity)
  have hmf (k : ℤ) : MemLp (fun ξ ↦ m k ξ *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) (hf2.toLp f)) ξ) 2 :=
    OAI.Analysis.Fourier.Wave.memLp_mul_bounded_symbol (m k) (hm k).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ξ ↦ hbound _)) _
  have he (k : ℤ) : dyadicAnnularConvolution χ k f =
      𝓕⁻ (fun ξ ↦ m k ξ * (𝓕 f) ξ) :=
    dyadicAnnularConvolution_eq_fourierInv hχ hc hf k
  constructor
  · intro k
    rw [he]
    exact memLp_inverse_fourier_mul_repr (hf2.toLp f) hf2.coeFn_toLp (hm k) (hcm k) hf (hmf k)
  · intro s
    simp_rw [he]
    apply integral_sum_norm_sq_inverse_fourier_mul_le s m hm hcm hf (hf2.toLp f) hf2.coeFn_toLp hmf
    exact Filter.Eventually.of_forall (fun ξ ↦
      sum_sq_dyadic_annular_symbol_le χ hband hM hbound s ((2 * Real.pi) • ξ))

end OAI.Analysis.Fourier.BochnerRiesz
