import OAI.Analysis.Fourier.SquareFunction.CubeKernels
import OAI.Analysis.Fourier.SquareFunction.ScaleVectors
import OAI.Analysis.Fourier.SquareFunction.ScaleDecomposition
import OAI.Analysis.Fourier.SquareFunction.SharpEnvelope
import OAI.Analysis.Fourier.SquareFunction.MiddleAverage

open OAI.Analysis.Fourier.Wave

/-! The actual low and high convolution vectors on a cube. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem norm_le_of_enorm_product {H : Type*} [NormedAddCommGroup H]
    {u : H} {A : ℝ} {B D : ℝ≥0∞} (hA : 0 ≤ A) (hB : B ≠ ∞) (hD : D ≠ ∞)
    (h : ‖u‖ₑ ≤ ENNReal.ofReal A * (B * D)) :
    ‖u‖ ≤ A * (B.toReal * D.toReal) := by
  have ht : ENNReal.ofReal A * (B * D) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hB hD)
  have hh := ENNReal.toReal_mono ht h
  simpa only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] using hh

theorem component_maximal_le_vector_maximal {n : ℕ} {I : Type*} [Fintype I]
    (f : I → Space n → ℂ) (i : I) (z : Space n) :
    ballMaximal volume (fun y => ‖f i y‖ₑ) z ≤
      ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z := by
  apply ballMaximal_mono
  intro y
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (component_norm_le_vectorNorm (fun i => f i y) i)

/-- The entire low vector enjoys a geometric gain, independent of the
number of scales. The derivative estimate is the one in the source lemma. -/
theorem low_cube_vector {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (s : Finset ℤ) (Q : BoxIntegral.Box (Fin n)) {d q C : ℝ}
    (hd : 0 < d) (hside : ∀ i, Q.upper i - Q.lower i = d)
    (hq : (n : ℝ) < q) (hC : 0 ≤ C)
    (K : s → Space n → H) (f : s → Space n → ℂ)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hB : ∀ i, BddAbove (range fun x => ‖K i x‖))
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (f i))
    {j L : ℤ} (hL : 0 ≤ L) (hj : (2 : ℝ) ^ j * (2 * (((n : ℝ) + 1) * d)) ≤ 1)
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q)
    (hM : ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z ≠ ∞) :
    vectorNorm (lowScaleDifference Subtype.val j L
      (fun i => convolveKernel (K i) (f i) x)
      (fun i => convolveKernel (K i) (f i) (cubeCorner Q))) ≤
      Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) *
        (C * 2 ^ q * (polynomialKernelMass n q).toReal *
          (ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z).toReal) := by
  classical
  let M := ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z
  let m := (polynomialKernelMass n q).toReal
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
      hC has (hKd i) (hK i) (hB i) (hfm i) (hfi i) hx hz
    have hh' : ‖convolveKernel (K i) (f i) x - convolveKernel (K i) (f i) (cubeCorner Q)‖ₑ ≤
        ENNReal.ofReal (C * 2 ^ q * (2 : ℝ) ^ (i.val - j)) * (polynomialKernelMass n q * M) := by
      apply hh.trans
      apply mul_le_mul
      · apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left hfactor (show 0 ≤ C * 2 ^ q by positivity)]
      · exact mul_le_mul_right (component_maximal_le_vector_maximal f i z) _
      · exact bot_le
      · exact bot_le
    have hn := norm_le_of_enorm_product (by positivity : 0 ≤ C * 2 ^ q * (2 : ℝ) ^ (i.val - j))
      (polynomialKernelMass_lt_top hq).ne hM hh'
    simp only [lowScaleDifference, hi, ite_true]
    convert hn using 1 ; ring
  · simp only [lowScaleDifference, hi, ite_false, norm_zero, zero_mul, le_refl]

/-- The off-diagonal high vector has the same summable scale gain. Here the
one spare decay power is used; the remaining kernel still has exponent `>n`. -/
theorem high_cube_vector {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (s : Finset ℤ) (Q : BoxIntegral.Box (Fin n)) {d q C : ℝ}
    (hd : 0 < d) (hside : ∀ i, Q.upper i - Q.lower i = d)
    (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (K : s → Space n → H) (f : s → Space n → ℂ)
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : ∀ i, Measurable (f i))
    {j L : ℤ} (hj : 1 / 2 < (2 : ℝ) ^ j * (2 * (((n : ℝ) + 1) * d)))
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q)
    (hM : ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z ≠ ∞) :
    vectorNorm (highScaleTerm Subtype.val j L (fun i => convolveKernel (K i)
      ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)))ᶜ.indicator (f i)) x)) ≤
      Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) *
        (C * 2 ^ q * (polynomialKernelMass n (q - 1)).toReal *
          (ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z).toReal) := by
  classical
  let M := ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z
  apply high_scale_vector_le s (j := j) (L := L) _ (by positivity)
  intro i
  by_cases hi : j + L ≤ i.val
  · have ha : 0 < (2 : ℝ) ^ i.val := zpow_pos (by norm_num) _
    have hr : 0 < q - 1 := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hfactor : ((2 : ℝ) ^ i.val * (4 * (((n : ℝ) + 1) * d)))⁻¹ ≤
        (2 : ℝ) ^ (-(i.val - j)) := by
      convert reference_tail_inverse hj i.val using 1 ; congr 2 ; ring
    have hh := tail_convolution_on_cube Q hd hside ha hr (by linarith : q - 1 ≤ q)
      hC (hK i) (hfm i) hx hz
    rw [show q - 1 - q = (-1 : ℝ) by ring, Real.rpow_neg_one] at hh
    have hh' : ‖convolveKernel (K i)
        ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)))ᶜ.indicator (f i)) x‖ₑ ≤
        ENNReal.ofReal (C * 2 ^ q * (2 : ℝ) ^ (-(i.val - j))) *
          (polynomialKernelMass n (q - 1) * M) := by
      apply hh.trans
      apply mul_le_mul
      · apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      · exact mul_le_mul_right (component_maximal_le_vector_maximal f i z) _
      · exact bot_le
      · exact bot_le
    have hn := norm_le_of_enorm_product (by positivity : 0 ≤ C * 2 ^ q * (2 : ℝ) ^ (-(i.val - j)))
      (polynomialKernelMass_lt_top (show (n : ℝ) < q - 1 by linarith)).ne hM hh'
    simp only [highScaleTerm, hi, ite_true]
    convert hn using 1 ; ring
  · simp only [highScaleTerm, hi, ite_false, norm_zero, zero_mul, le_refl]

theorem middle_subtype_card (s : Finset ℤ) (j L : ℤ) :
    ((Finset.univ : Finset s).filter (fun i => j - L < i.val ∧ i.val < j + L)).card ≤
      (2 * L).toNat := by
  classical
  have he : ((Finset.univ : Finset s).filter (fun i => j - L < i.val ∧ i.val < j + L)).card =
      (s.filter (fun k => j - L < k ∧ k < j + L)).card := by
    have hh := sum_mask_over_subtype (s := s) (fun k => j - L < k ∧ k < j + L) (fun _ => (1 : ℝ))
    rw [← Finset.sum_filter] at hh
    simpa using hh
  rw [he]
  exact middle_window_card

/-- The middle window on an arbitrary genuine cube has the desired
`(2L)^(1/2-1/p)` loss, irrespective of the total number of scales. -/
theorem middle_cube_vector_average {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (s : Finset ℤ) (Q : BoxIntegral.Box (Fin n)) {d : ℝ}
    (hd : 0 < d) (hside : ∀ i, Q.upper i - Q.lower i = d)
    (u : s → Space n → H) (hu : ∀ i, Measurable (u i))
    (j L : ℤ) {p : ℝ} (hp : 2 ≤ p)
    {z : Space n} (hz : z ∈ euclideanBox Q) :
    (∫⁻ x in euclideanBox Q, ENNReal.ofReal (vectorNorm
      (middleScaleTerm Subtype.val j L (fun i => u i x)))) / volume (euclideanBox Q) ≤
      (cubeBallRatio n ^ (1 / 2 : ℝ) * ((2 * L).toNat : ℝ≥0∞) ^ (1 / 2 - 1 / p)) *
        (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p) := by
  classical
  have hQball : euclideanBox Q ⊆ ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d)) := by
    intro y hy
    have hy0 := euclideanBox_subset_ball Q hd hside hy
    have hr : 0 < ((n : ℝ) + 1) * d := by positivity
    exact mem_ball.mpr ((mem_ball.mp hy0).trans_le (by linarith))
  have h := masked_middle_vector_average u hu (D := cubeBallRatio n)
    (fun i => j - L < i.val ∧ i.val < j + L)
    (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
    (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
    hQball (hQball hz)
    (by simpa only [cubeBallRatio, mul_assoc] using
      (volume_enlarged_cube_ball Q hd (show 0 < 8 * ((n : ℝ) + 1) by positivity) hside).le) hp
  apply h.trans
  apply mul_le_mul_left
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow
  · exact_mod_cast middle_subtype_card s j L
  · have hpp : 0 < p := by linarith
    have hdiv : 1 / p ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hp
    linarith

end OAI.Analysis.Fourier.SquareFunction
