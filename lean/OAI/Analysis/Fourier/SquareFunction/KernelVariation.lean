import OAI.Analysis.Fourier.SquareFunction.EuclideanKernel
import OAI.Analysis.Fourier.SquareFunction.EuclideanSharp

open OAI.Analysis.Fourier.Wave

/-! Mean-value and maximal-function bounds for the low-frequency group. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Metric
open scoped ENNReal

/-- Polynomial decay changes by a bounded factor within one rescaled unit. -/
theorem polynomial_decay_nearby {E : Type*} [NormedAddCommGroup E]
    {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) {u v : E}
    (huv : a * dist u v ≤ 1) :
    (a * ‖u‖ + 1) ^ (-q) ≤ (2 : ℝ) ^ q * (a * ‖v‖ + 1) ^ (-q) := by
  have htri : ‖v‖ ≤ ‖u‖ + dist u v := by
    simpa only [dist_eq_norm, norm_sub_rev u v] using norm_le_insert' v u
  have hb : (a * ‖v‖ + 1) / 2 ≤ a * ‖u‖ + 1 := by
    have h := mul_le_mul_of_nonneg_left htri ha
    nlinarith [norm_nonneg u, mul_nonneg ha (norm_nonneg u)]
  calc
    _ ≤ ((a * ‖v‖ + 1) / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr hq)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num) (-q),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring

/-- A decaying derivative controls oscillation between two points lying
within one rescaled unit of an arbitrary comparison point. -/
theorem kernel_variation_of_deriv {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a q C : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (hC : 0 ≤ C)
    {K : Space n → H} (hKd : Differentiable ℝ K)
    (hK : ∀ u, ‖fderiv ℝ K u‖ ≤ C * (a ^ n * a) * (a * ‖u‖ + 1) ^ (-q))
    {x c z : Space n} (hx : a * dist x z ≤ 1) (hc : a * dist c z ≤ 1) :
    ‖K x - K c‖ ≤ (C * 2 ^ q * a * dist x c) *
      (a ^ n * (a * ‖z‖ + 1) ^ (-q)) := by
  have hxb : x ∈ closedBall z (1 / a) := (mem_closedBall).2 ((le_div_iff₀ ha).2 (by nlinarith [hx]))
  have hcb : c ∈ closedBall z (1 / a) := (mem_closedBall).2 ((le_div_iff₀ ha).2 (by nlinarith [hc]))
  have hb (u : Space n) (hu : u ∈ closedBall z (1 / a)) :
      ‖fderiv ℝ K u‖ ≤ C * (a ^ n * a) * (2 ^ q * (a * ‖z‖ + 1) ^ (-q)) := by
    apply (hK u).trans
    apply mul_le_mul_of_nonneg_left
    · apply polynomial_decay_nearby hq ha.le
      have hu' := (le_div_iff₀ ha).1 (mem_closedBall.mp hu)
      nlinarith
    · positivity
  have h := (convex_closedBall z (1 / a)).norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hKd u) hb hcb hxb
  calc
    _ ≤ (C * (a ^ n * a) * (2 ^ q * (a * ‖z‖ + 1) ^ (-q))) * ‖x - c‖ := h
    _ = _ := by rw [dist_eq_norm]; ring

/-- Actual convolution oscillation, bounded by the scalar maximal function
at any nearby point. This supplies the small factor `a * dist x c`. -/
theorem convolution_variation_le_maximal {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {a q C : ℝ} (ha : 0 < a) (hq : 0 < q) (hC : 0 ≤ C)
    {K : Space n → H} (hKd : Differentiable ℝ K)
    (hK : ∀ u, ‖fderiv ℝ K u‖ ≤ C * (a ^ n * a) * (a * ‖u‖ + 1) ^ (-q))
    {f : Space n → ℂ} (hf : Measurable f) {x c z : Space n}
    (hx : a * dist x z ≤ 1) (hc : a * dist c z ≤ 1)
    (hix : Integrable (fun y => f y • K (x - y)))
    (hic : Integrable (fun y => f y • K (c - y))) :
    ‖(∫ y, f y • K (x - y)) - ∫ y, f y • K (c - y)‖ₑ ≤
      ENNReal.ofReal (C * 2 ^ q * a * dist x c) *
        (polynomialKernelMass n q * ballMaximal volume (fun y => ‖f y‖ₑ) z) := by
  let D : Space n → H := fun w => K (w + (x - z)) - K (w + (c - z))
  have hD (w : Space n) : ‖D w‖ₑ ≤ ENNReal.ofReal (C * 2 ^ q * a * dist x c) *
      (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * ‖w‖ + 1) ^ (-q))) := by
    have h := kernel_variation_of_deriv ha hq.le hC hKd hK
      (x := w + (x - z)) (c := w + (c - z)) (z := w)
      (by simpa only [dist_eq_norm, add_sub_cancel_left] using hx)
      (by simpa only [dist_eq_norm, add_sub_cancel_left] using hc)
    have hd : dist (w + (x - z)) (w + (c - z)) = dist x c := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rw [hd] at h
    simpa only [D, ofReal_norm, ENNReal.ofReal_mul (by positivity : 0 ≤ C * 2 ^ q * a * dist x c),
      ENNReal.ofReal_mul (pow_nonneg ha.le n)] using ENNReal.ofReal_le_ofReal h
  have h := enorm_kernel_convolution_le_maximal ha hq hf hD z
  rw [← integral_sub hix hic]
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [D]
  rw [smul_sub]
  congr 2 <;> abel_nf

end OAI.Analysis.Fourier.SquareFunction
