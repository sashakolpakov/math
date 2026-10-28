import OAI.Analysis.Fourier.BochnerRiesz.LittlewoodPaley
import OAI.Analysis.Fourier.BochnerRiesz.SquareEnergy

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem continuous_dyadicAnnularConvolution {n : ℕ} {χ f : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hf : Integrable f) (k : ℤ) :
    Continuous (dyadicAnnularConvolution χ k f) := by
  rw [dyadicAnnularConvolution_eq_fourierInv hχ hc hf k]
  have hm : Continuous (fun ξ : Space n ↦ χ ((2 : ℝ) ^ (-k) • ((2 * Real.pi) • ξ))) := by
    fun_prop
  have hcm : HasCompactSupport (fun ξ : Space n ↦ χ ((2 : ℝ) ^ (-k) • ((2 * Real.pi) • ξ))) :=
    (hc.comp_smul (ne_of_gt (zpow_pos (by norm_num) (-k)))).comp_smul (by positivity)
  exact continuous_fourierInv_of_integrable
    ((hm.mul (continuous_fourier_of_integrable hf)).integrable_of_hasCompactSupport hcm.mul_right)

theorem eLpNorm_dyadicAnnularConvolution_vector_two {n N : ℕ} {χ f : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hband : ∀ ξ, χ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ ξ, ‖χ ξ‖ ≤ M)
    (hf : Integrable f) (hf2 : MemLp f 2) (s : Finset ℤ) :
    eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ dyadicAnnularConvolution χ i.val f x)) 2 volume ≤
      ENNReal.ofReal ((2 * (N : ℝ) + 1) * M ^ 2) ^ (1 / 2 : ℝ) * eLpNorm f 2 volume := by
  have H := dyadicAnnularConvolution_L2 hχ hc hband hM hbound hf hf2
  have hv (i : s) : Measurable (dyadicAnnularConvolution χ i.val f) :=
    (continuous_dyadicAnnularConvolution hχ hc hf i.val).measurable
  have hn := eLpNorm_vectorNorm_two_eq_energy (μ := (volume : Measure (Space n)))
    (fun i : s ↦ dyadicAnnularConvolution χ i.val f) hv (fun i ↦ H.1 i.val)
  rw [hn, eLpNorm_two_eq_energy hf2]
  have he : (∫ x, ∑ i : s, ‖dyadicAnnularConvolution χ i.val f x‖ ^ 2) =
      ∫ x, ∑ k ∈ s, ‖dyadicAnnularConvolution χ k f x‖ ^ 2 := by
    congr 1
    funext x
    exact Finset.sum_coe_sort s (fun k : ℤ ↦ ‖dyadicAnnularConvolution χ k f x‖ ^ 2)
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (((2 * (N : ℝ) + 1) * M ^ 2) * ∫ x, ‖f x‖ ^ 2) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (H.2 s)) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end OAI.Analysis.Fourier.BochnerRiesz
