import OAI.Analysis.Fourier.Restriction.PhaseInterpolation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def phaseInterpolationConstant (q s : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-q * s))) *
    ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (1 + -q * s))⁻¹)

theorem phaseInterpolationConstant_ne_top {q s : ℝ} {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    phaseInterpolationConstant q s C ≠ ⊤ := by
  unfold phaseInterpolationConstant
  finiteness

theorem finitePhaseSum_strong_bound {n : ℕ} (E : Finset (Space n))
    {p q s : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hs : 0 ≤ s) (hqs : q * s < 1)
    {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum S a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          C * ENNReal.ofReal ((S.card : ℝ) ^ s)) (a : Space n → ℂ) :
    eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      phaseInterpolationConstant q s C * ENNReal.ofReal ((∑ z ∈ E, ‖a z‖ ^ q) ^ (1 / q)) := by
  let S : ℝ := ∑ z ∈ E, ‖a z‖ ^ q
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hS : S = 0
  · have ha : ∀ z ∈ E, a z = 0 := by
      intro z hz
      have H : ‖a z‖ ^ q ≤ 0 := by
        calc
          _ ≤ S := Finset.single_le_sum (fun w _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hz
          _ = 0 := hS
      have Hzero : ‖a z‖ ^ q = 0 := le_antisymm H (Real.rpow_nonneg (norm_nonneg _) _)
      have hn : ‖a z‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) hq.ne').mp Hzero
      exact norm_eq_zero.mp hn
    have hP : finitePhaseSum E a = 0 := by
      funext ξ
      apply Finset.sum_eq_zero
      intro z hz
      rw [ha z hz, zero_mul]
    rw [hP, eLpNorm_zero]
    exact zero_le
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
  let N := S ^ (1 / q)
  have hNp : 0 < N := Real.rpow_pos_of_pos hSp _
  have hNq : N ^ q = S := by
    dsimp [N]
    rw [← Real.rpow_mul hSp.le, one_div_mul_cancel hq.ne', Real.rpow_one]
  let b : Space n → ℂ := fun z ↦ ((N⁻¹ : ℝ) : ℂ) * a z
  have hsum : (∑ z ∈ E, ‖b z‖ ^ q) ≤ 1 := by
    have he (z : Space n) : ‖b z‖ ^ q = (N ^ q)⁻¹ * ‖a z‖ ^ q := by
      dsimp [b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNp),
        Real.mul_rpow (inv_nonneg.mpr hNp.le) (norm_nonneg _), Real.inv_rpow hNp.le]
    simp_rw [he]
    rw [← Finset.mul_sum, hNq]
    change S⁻¹ * S ≤ 1
    rw [inv_mul_cancel₀ hS]
  have H := finitePhaseSum_normalized_bound E hp hq hs hqs hres b hsum
  have he : a = (fun z ↦ (N : ℂ) * b z) := by
    funext z
    dsimp [b]
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hNp.ne'), one_mul]
  have hPeq : finitePhaseSum E a = (N : ℂ) • finitePhaseSum E b := by
    conv_lhs => rw [he]
    exact finitePhaseSum_const_mul E b (N : ℂ)
  rw [hPeq, eLpNorm_const_smul]
  have hn : ‖(N : ℂ)‖ₑ = ENNReal.ofReal N := by
    simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp]
  rw [hn]
  calc
    _ ≤ ENNReal.ofReal N * phaseInterpolationConstant q s C := by
      gcongr
      exact H
    _ = _ := mul_comm _ _

end OAI.Analysis.Fourier.Restriction
