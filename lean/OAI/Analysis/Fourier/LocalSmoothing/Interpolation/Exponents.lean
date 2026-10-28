import OAI.Analysis.Fourier.LocalSmoothing.Definitions
import Mathlib

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem criticalExponent_gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  apply (lt_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).mpr
  nlinarith

theorem smoothingOrder_of_le_critical {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp : 0 < p) (hpq : p ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = 0 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hmul := (le_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).mp hpq
  have hdiv : ((n:ℝ)-1)/2 ≤ n/p := (le_div_iff₀ hp).mpr (by nlinarith)
  exact max_eq_left (sub_nonpos.mpr hdiv)

theorem smoothingOrder_of_ge_critical {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ p) : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = ((n:ℝ)-1)/2-n/p := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := lt_trans (by norm_num) ((criticalExponent_gt_two hn).trans_le hqp)
  have hmul := (div_le_iff₀ (by linarith : 0 < (n:ℝ)-1)).mp hqp
  have hdiv : (n:ℝ)/p ≤ (n-1)/2 := (div_le_iff₀ hp).mpr (by nlinarith)
  exact max_eq_right (sub_nonneg.mpr hdiv)

theorem high_frequency_exponent {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ p) :
    (-((n:ℝ)-1)/2) * (1-OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n/p) = -OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := lt_trans (by norm_num) ((criticalExponent_gt_two hn).trans_le hqp)
  rw [smoothingOrder_of_ge_critical hn hqp]
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  have hn0 : (n:ℝ)-1 ≠ 0 := by linarith
  field_simp [hn0, hp.ne']


theorem interpolation_factor_le {C D L h a θ : ℝ} {k : ℕ}
    (hC : 0 < C) (hD : 0 < D) (hL : 1 ≤ L) (hh : 0 < h)
    (_ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (C * L ^ k) ^ θ * (D * h ^ a) ^ (1-θ) ≤
      (C ^ θ * D ^ (1-θ)) * h ^ (a*(1-θ)) * L ^ k := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  rw [Real.mul_rpow hC.le (pow_nonneg hL0 _),
    Real.mul_rpow hD.le (Real.rpow_nonneg hh.le _),
    ← Real.rpow_natCast L k, ← Real.rpow_mul hL0, ← Real.rpow_mul hh.le]
  have hb : L ^ ((k:ℝ)*θ) ≤ L ^ (k:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (mul_le_of_le_one_right (Nat.cast_nonneg k) hθ1)
  calc
    _ = (C^θ * D^(1-θ)) * h^(a*(1-θ)) * L^((k:ℝ)*θ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

theorem logarithm_weight_one_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    1 ≤ 1 + Real.log (1/h) := by
  have hi : 1 ≤ 1/h := (le_div_iff₀ hh).mpr (by simpa using h1)
  linarith [Real.log_nonneg hi]

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
