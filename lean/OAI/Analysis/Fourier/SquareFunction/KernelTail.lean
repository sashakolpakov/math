import OAI.Analysis.Fourier.SquareFunction.KernelVariation

open OAI.Analysis.Fourier.Wave

/-! Off-diagonal decay for the high-frequency group. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Metric
open scoped ENNReal

theorem polynomial_decay_tail {a R q r t : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hqr : r ≤ q) (ht : R ≤ t) :
    (a * t + 1) ^ (-q) ≤ (a * R) ^ (r - q) * (a * t + 1) ^ (-r) := by
  have ht0 : 0 < t := hR.trans_le ht
  have hb : 0 < a * t + 1 := by positivity
  have hpow : (a * t + 1) ^ (r - q) ≤ (a * R) ^ (r - q) := by
    apply Real.rpow_le_rpow_of_nonpos (mul_pos ha hR) _ (sub_nonpos.mpr hqr)
    nlinarith
  calc
    _ = (a * t + 1) ^ (r - q) * (a * t + 1) ^ (-r) := by
      rw [← Real.rpow_add hb]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb.le _)

theorem polynomial_decay_of_half_shift {E : Type*} [NormedAddCommGroup E]
    {a q R : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    {w v : E} (hw : R ≤ ‖w‖) (hv : ‖v‖ ≤ R / 2) :
    (a * ‖w + v‖ + 1) ^ (-q) ≤ 2 ^ q * (a * ‖w‖ + 1) ^ (-q) := by
  have htri : ‖w‖ ≤ ‖w + v‖ + ‖v‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (w + v) v
  have hrel : ‖w‖ ≤ 2 * ‖w + v‖ := by linarith
  have hb : (a * ‖w‖ + 1) / 2 ≤ a * ‖w + v‖ + 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hrel ha]
  calc
    _ ≤ ((a * ‖w‖ + 1) / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr hq)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num) (-q),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring

/-- A polynomial tail may be traded for a small scale factor while retaining
an integrable polynomial kernel. The exponents `q > r > n` can be chosen
once and for all; with `q=n+3`, taking `r=n+1` gives quadratic tail gain. -/
theorem enorm_truncated_shifted_kernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] {a R q r C : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hq : 0 ≤ q) (hqr : r ≤ q) (hC : 0 ≤ C)
    {K : Space n → H}
    (hK : ∀ u, ‖K u‖ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q))
    {v : Space n} (hv : ‖v‖ ≤ R / 2) (w : Space n) :
    ‖(if R ≤ ‖w‖ then K (w + v) else 0)‖ₑ ≤
      ENNReal.ofReal (C * 2 ^ q * (a * R) ^ (r - q)) *
        (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * ‖w‖ + 1) ^ (-r))) := by
  split_ifs with hw
  · have h : ‖K (w + v)‖ ≤ (C * 2 ^ q * (a * R) ^ (r - q)) *
        (a ^ n * (a * ‖w‖ + 1) ^ (-r)) := by
      calc
        _ ≤ C * a ^ n * (2 ^ q * (a * ‖w‖ + 1) ^ (-q)) :=
          (hK _).trans (mul_le_mul_of_nonneg_left
            (polynomial_decay_of_half_shift ha.le hq hw hv) (by positivity))
        _ ≤ C * a ^ n * (2 ^ q * ((a * R) ^ (r - q) * (a * ‖w‖ + 1) ^ (-r))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (polynomial_decay_tail ha hR hqr hw) (by positivity)
        _ = _ := by ring
    simpa only [ofReal_norm, ENNReal.ofReal_mul
      (by positivity : 0 ≤ C * 2 ^ q * (a * R) ^ (r - q)),
      ENNReal.ofReal_mul (pow_nonneg ha.le n)] using ENNReal.ofReal_le_ofReal h
  · simp only [enorm_zero]
    exact bot_le

/-- Off-diagonal convolutions enjoy the tail scale gain uniformly in the
center and the displacement of the output point. -/
theorem tail_convolution_le_maximal {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {a R q r C : ℝ} (ha : 0 < a) (hR : 0 < R) (hr : 0 < r)
    (hqr : r ≤ q) (hC : 0 ≤ C) {K : Space n → H}
    (hK : ∀ u, ‖K u‖ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q))
    {f : Space n → ℂ} (hf : Measurable f) {x z : Space n}
    (hx : dist x z ≤ R / 2)
    (hfzero : ∀ y, dist y z < R → f y = 0) :
    ‖∫ y, f y • K (x - y)‖ₑ ≤
      ENNReal.ofReal (C * 2 ^ q * (a * R) ^ (r - q)) *
        (polynomialKernelMass n r * ballMaximal volume (fun y => ‖f y‖ₑ) z) := by
  let D : Space n → H := fun w => if R ≤ ‖w‖ then K (w + (x - z)) else 0
  have hD := enorm_truncated_shifted_kernel ha hR (hr.le.trans hqr) hqr hC hK
    (v := x - z) (by simpa only [dist_eq_norm] using hx)
  have h := enorm_kernel_convolution_le_maximal ha hr hf hD z
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  split_ifs with hy
  · congr 2
    abel
  · have hf0 := hfzero y (by simpa only [dist_eq_norm, norm_sub_rev y z] using lt_of_not_ge hy)
    simp only [hf0, zero_smul, smul_zero]

end OAI.Analysis.Fourier.SquareFunction
