import OAI.Analysis.Fourier.SquareFunction.CubeOscillation

open OAI.Analysis.Fourier.Wave

/-! The low and far-high vector estimates when every kernel acts on one
common input. Their maximal envelope is that of the single input, not of
its repeated finite vector. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem low_cube_common_input {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (s : Finset ℤ) (Q : BoxIntegral.Box (Fin n)) {d q C : ℝ}
    (hd : 0 < d) (hside : ∀ i, Q.upper i - Q.lower i = d)
    (hq : (n : ℝ) < q) (hC : 0 ≤ C)
    (K : s → Space n → H) (f : Space n → ℂ)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hB : ∀ i, BddAbove (range fun x => ‖K i x‖))
    (hfm : Measurable f) (hfi : Integrable f)
    {j L : ℤ} (hL : 0 ≤ L) (hj : (2 : ℝ) ^ j * (2 * (((n : ℝ) + 1) * d)) ≤ 1)
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q)
    (hM : ballMaximal volume (fun y => ‖f y‖ₑ) z ≠ ∞) :
    vectorNorm (lowScaleDifference Subtype.val j L
      (fun i => convolveKernel (K i) f x)
      (fun i => convolveKernel (K i) f (cubeCorner Q))) ≤
      scaleKernelConstant n q q C L * (ballMaximal volume (fun y => ‖f y‖ₑ) z).toReal := by
  classical
  let M := ballMaximal volume (fun y => ‖f y‖ₑ) z
  have hv : vectorNorm (lowScaleDifference Subtype.val j L
      (fun i => convolveKernel (K i) f x) (fun i => convolveKernel (K i) f (cubeCorner Q))) ≤
      Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) * (C * 2 ^ q * (polynomialKernelMass n q).toReal * M.toReal) := by
    apply low_scale_vector_le s (j := j) (L := L) _ (by positivity)
    intro i
    by_cases hi : i.val ≤ j - L
    · have hij : i.val ≤ j := by omega
      have ha : 0 < (2 : ℝ) ^ i.val := zpow_pos (by norm_num) _
      have has : (2 : ℝ) ^ i.val * (2 * (n : ℝ) * d) ≤ 1 := by
        apply le_trans _ (reference_scale_unit hj hij)
        apply mul_le_mul_of_nonneg_left _ ha.le
        nlinarith
      have hfactor : (2 : ℝ) ^ i.val * ((n : ℝ) * d) ≤ (2 : ℝ) ^ (i.val - j) := by
        apply le_trans _ (reference_scale_upper hj i.val)
        apply mul_le_mul_of_nonneg_left _ ha.le
        nlinarith [mul_nonneg (Nat.cast_nonneg n) hd.le]
      have hh := low_convolution_on_cube Q hd hside ha (lt_of_le_of_lt (Nat.cast_nonneg n) hq)
        hC has (hKd i) (hK i) (hB i) hfm hfi hx hz
      have hh' : ‖convolveKernel (K i) f x - convolveKernel (K i) f (cubeCorner Q)‖ₑ ≤
          ENNReal.ofReal (C * 2 ^ q * (2 : ℝ) ^ (i.val - j)) * (polynomialKernelMass n q * M) := by
        apply hh.trans
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left hfactor (show 0 ≤ C * 2 ^ q by positivity)]
      have hn := norm_le_of_enorm_product (by positivity : 0 ≤ C * 2 ^ q * (2 : ℝ) ^ (i.val - j))
        (polynomialKernelMass_lt_top hq).ne hM hh'
      simp only [lowScaleDifference, hi, ite_true]
      convert hn using 1 ; ring
    · simp only [lowScaleDifference, hi, ite_false, norm_zero, zero_mul, le_refl]
  convert hv using 1
  unfold scaleKernelConstant
  ring

theorem high_cube_common_input {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (s : Finset ℤ) (Q : BoxIntegral.Box (Fin n)) {d q C : ℝ}
    (hd : 0 < d) (hside : ∀ i, Q.upper i - Q.lower i = d)
    (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (K : s → Space n → H) (f : Space n → ℂ)
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : Measurable f)
    {j L : ℤ} (hj : 1 / 2 < (2 : ℝ) ^ j * (2 * (((n : ℝ) + 1) * d)))
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q)
    (hM : ballMaximal volume (fun y => ‖f y‖ₑ) z ≠ ∞) :
    vectorNorm (highScaleTerm Subtype.val j L (fun i => convolveKernel (K i)
      ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)))ᶜ.indicator f) x)) ≤
      scaleKernelConstant n q (q - 1) C L * (ballMaximal volume (fun y => ‖f y‖ₑ) z).toReal := by
  classical
  let M := ballMaximal volume (fun y => ‖f y‖ₑ) z
  have hv : vectorNorm (highScaleTerm Subtype.val j L (fun i => convolveKernel (K i)
      ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)))ᶜ.indicator f) x)) ≤
      Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) * (C * 2 ^ q * (polynomialKernelMass n (q - 1)).toReal * M.toReal) := by
    apply high_scale_vector_le s (j := j) (L := L) _ (by positivity)
    intro i
    by_cases hi : j + L ≤ i.val
    · have ha : 0 < (2 : ℝ) ^ i.val := zpow_pos (by norm_num) _
      have hr : 0 < q - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hfactor : ((2 : ℝ) ^ i.val * (4 * (((n : ℝ) + 1) * d)))⁻¹ ≤
          (2 : ℝ) ^ (-(i.val - j)) := by
        convert reference_tail_inverse hj i.val using 1 ; congr 2 ; ring
      have hh := tail_convolution_on_cube Q hd hside ha hr (by linarith : q - 1 ≤ q)
        hC (hK i) hfm hx hz
      rw [show q - 1 - q = (-1 : ℝ) by ring, Real.rpow_neg_one] at hh
      have hh' : ‖convolveKernel (K i)
          ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)))ᶜ.indicator f) x‖ₑ ≤
          ENNReal.ofReal (C * 2 ^ q * (2 : ℝ) ^ (-(i.val - j))) *
            (polynomialKernelMass n (q - 1) * M) := by
        apply hh.trans
        apply mul_le_mul_left
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfactor (by positivity))
      have hn := norm_le_of_enorm_product (by positivity : 0 ≤ C * 2 ^ q * (2 : ℝ) ^ (-(i.val - j)))
        (polynomialKernelMass_lt_top (show (n : ℝ) < q - 1 by linarith)).ne hM hh'
      simp only [highScaleTerm, hi, ite_true]
      convert hn using 1 ; ring
    · simp only [highScaleTerm, hi, ite_false, norm_zero, zero_mul, le_refl]
  convert hv using 1
  unfold scaleKernelConstant
  ring

end OAI.Analysis.Fourier.SquareFunction
