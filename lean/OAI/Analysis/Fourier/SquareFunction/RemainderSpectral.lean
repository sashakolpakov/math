import OAI.Analysis.Fourier.SquareFunction.Radius.DyadicReverse
import OAI.Analysis.Fourier.SquareFunction.Square.L2
import OAI.Analysis.Fourier.SquareFunction.Scaling
import OAI.Analysis.Fourier.BochnerRiesz.RadialPartition

open OAI.Analysis.Fourier.Wave

/-! Uniform aggregate spectral energy for the smooth interior remainder.
Its quadratic zero at frequency zero is automatically accounted for by
domination by the full Stein multiplier. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem enorm_real_sq (a : ℝ) : ‖(a : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem radiusMultiplier_dyadic_energy_le {α ρ : ℝ}
    (hα : 1 / 2 < α) (hρ : 0 ≤ ρ) :
    (∑' k : ℤ, ∫⁻ r in Icc (1 : ℝ) 2,
      ‖(radiusMultiplier α (((2 : ℝ) ^ k)⁻¹ * ρ) r : ℂ)‖ₑ ^ 2) ≤
      2 * ENNReal.ofReal (α / (2 * α - 1)) := by
  by_cases hz : ρ = 0
  · simp only [hz, mul_zero, radiusMultiplier, zero_div, mul_zero, zero_mul, ite_self, Complex.ofReal_zero, enorm_zero,
      zero_pow (by norm_num : 2 ≠ 0), lintegral_zero, tsum_zero]
    positivity
  have hp : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
  let F : ℝ → ℝ≥0∞ := fun r => ‖(radiusMultiplier α ρ r : ℂ)‖ₑ ^ 2
  have hm : Measurable F := by
    have hm' : Measurable (fun r : ℝ => radiusMultiplier α ρ r) :=
      (measurable_radiusMultiplier α).comp (measurable_const.prodMk measurable_id)
    exact (Complex.measurable_ofReal.comp hm').enorm.pow_const _
  have hs (k : ℤ) (r : ℝ) :
      radiusMultiplier α (((2 : ℝ) ^ k)⁻¹ * ρ) r =
        radiusMultiplier α ρ ((2 : ℝ) ^ k * r) := by
    have h := radiusMultiplier_scale (by positivity : 0 < (2 : ℝ) ^ k)
      α (((2 : ℝ) ^ k)⁻¹ * ρ) r
    rw [mul_inv_cancel_left₀ (by positivity : (2 : ℝ) ^ k ≠ 0)] at h
    exact h.symm
  simp_rw [hs]
  have he : (∫⁻ r in Ioi (0 : ℝ), F r / ENNReal.ofReal r) =
      ENNReal.ofReal (α / (2 * α - 1)) := by
    rw [← radius_lintegral hp hα]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only [F]
    rw [enorm_real_sq, ENNReal.ofReal_div_of_pos hr]
  exact (radius_dyadic_le_two_ratio F hm).trans_eq (by rw [he])

theorem remainder_spectral_energy_le {n : ℕ} {α : ℝ} (hα : 1 / 2 < α)
    (A : ℝ × Space n → ℂ)
    (hA : ∀ r ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
      ‖A (r, ξ)‖ₑ ≤ ‖(radiusMultiplier α ‖ξ‖ r : ℂ)‖ₑ)
    (s : Finset ℤ) (ξ : Space n) :
    (∑ k ∈ s, ∫⁻ r in Icc (1 : ℝ) 2,
      ‖A (r, ((2 : ℝ) ^ k)⁻¹ • ξ)‖ₑ ^ 2) ≤
      2 * ENNReal.ofReal (α / (2 * α - 1)) := by
  calc
    _ ≤ ∑ k ∈ s, ∫⁻ r in Icc (1 : ℝ) 2,
        ‖(radiusMultiplier α (((2 : ℝ) ^ k)⁻¹ * ‖ξ‖) r : ℂ)‖ₑ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply setLIntegral_mono' measurableSet_Icc
      intro r hr
      have h := pow_le_pow_left' (hA r hr (((2 : ℝ) ^ k)⁻¹ • ξ)) 2
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ k)⁻¹)] using h
    _ ≤ ∑' k : ℤ, ∫⁻ r in Icc (1 : ℝ) 2,
        ‖(radiusMultiplier α (((2 : ℝ) ^ k)⁻¹ * ‖ξ‖) r : ℂ)‖ₑ ^ 2 :=
      ENNReal.sum_le_tsum s
    _ ≤ _ := radiusMultiplier_dyadic_energy_le hα (norm_nonneg ξ)

theorem norm_remainder_symbol_le (α ρ r : ℝ) :
    ‖(radiusMultiplier α ρ r : ℂ) *
      (1 - (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) : ℂ))‖ₑ ≤
      ‖(radiusMultiplier α ρ r : ℂ)‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.nonneg
  have h1 : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) ≤ 1 :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.le_one
  rw [abs_of_nonneg (by linarith)]
  linarith

end OAI.Analysis.Fourier.SquareFunction
