import OAI.Analysis.Fourier.SquareFunction.CombiningScales
import OAI.Analysis.Fourier.SquareFunction.LogWindow

open OAI.Analysis.Fourier.Wave

/-! The geometric and logarithmic constants in combining dilates. -/

namespace OAI.Analysis.Fourier.SquareFunction

open scoped ENNReal
open _root_.MeasureTheory Set

theorem scaleKernelConstant_small {n : ℕ} {q r C δ : ℝ} {L : ℤ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hL : (2 : ℝ) ^ (-L) ≤ δ ^ (q + 1)) :
    scaleKernelConstant n q r (C * δ ^ (-q)) L ≤
      scaleKernelConstant n q r 1 0 * (C * δ) := by
  have hprod : δ ^ (-q) * δ ^ (q + 1) = δ := by
    rw [← Real.rpow_add hδ, show -q + (q + 1) = 1 by ring, Real.rpow_one]
  have hs : C * δ ^ (-q) * (2 : ℝ) ^ (-L) ≤ C * δ := by
    calc
      _ ≤ C * δ ^ (-q) * δ ^ (q + 1) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by rw [mul_assoc, hprod]
  calc
    _ = (Real.sqrt (4 / 3) * 2 ^ q * (polynomialKernelMass n r).toReal) *
        (C * δ ^ (-q) * (2 : ℝ) ^ (-L)) := by unfold scaleKernelConstant; ring
    _ ≤ (Real.sqrt (4 / 3) * 2 ^ q * (polynomialKernelMass n r).toReal) * (C * δ) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by simp only [scaleKernelConstant, neg_zero, zpow_zero, mul_one, one_mul]; ring

theorem ennreal_four_linear_le (a b c d x y z : ℝ≥0∞) :
    a * x + b * y + c * z + d * x ≤ (a + b + c + d) * (x + y + z) := by
  have hx : x ≤ x + y + z := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hy : y ≤ x + y + z := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hz : z ≤ x + y + z := le_add_left le_rfl
  calc
    _ ≤ a * (x + y + z) + b * (x + y + z) + c * (x + y + z) + d * (x + y + z) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul_right hx _) (mul_le_mul_right hy _))
        (mul_le_mul_right hz _)) (mul_le_mul_right hx _)
    _ = _ := by ring

noncomputable def combiningLogConstant (n : ℕ) (p q : ℝ) : ℝ≥0∞ :=
  sharpLpConstant n p *
    (ENNReal.ofReal (scaleKernelConstant n q q 1 0) * maximalLpConstant n p +
      (cubeBallRatio n ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (2 * (q + 1) / Real.log 2 + 4) ^ (1 / 2 - 1 / p)) * squareMaximalLpConstant n p +
      cubeBallRatio n ^ (1 / 2 : ℝ) * squareMaximalLpConstant n p +
      ENNReal.ofReal (scaleKernelConstant n q (q - 1) 1 0) * maximalLpConstant n p)

theorem convolutionEnvelopeConstant_log_bound {n : ℕ} {p q C δ : ℝ} {L : ℤ}
    (hp : 2 < p) (hq : 0 ≤ q) (hC : 0 ≤ C) (hδ : 0 < δ) (_ : δ ≤ 1)
    (hL : (2 : ℝ) ^ (-L) ≤ δ ^ (q + 1))
    (hcard : ((2 * L).toNat : ℝ) ≤
      (2 * (q + 1) / Real.log 2 + 4) * (1 + Real.log (1 / δ)))
    (B₂ Bₚ : ℝ≥0∞) :
    sharpLpConstant n p * convolutionEnvelopeConstant n p q (C * δ ^ (-q)) B₂ Bₚ L ≤
      combiningLogConstant n p q *
        (ENNReal.ofReal (C * δ) +
          ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) * Bₚ + B₂) := by
  have hθ : 0 ≤ 1 / 2 - 1 / p := by
    have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp.le
    linarith
  have hk : 0 ≤ 2 * (q + 1) / Real.log 2 + 4 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hc : ((2 * L).toNat : ℝ≥0∞) ^ (1 / 2 - 1 / p) ≤
      ENNReal.ofReal (2 * (q + 1) / Real.log 2 + 4) ^ (1 / 2 - 1 / p) *
        ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) := by
    have hh := ENNReal.ofReal_le_ofReal hcard
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hk] at hh
    exact (ENNReal.rpow_le_rpow hh hθ).trans_eq (ENNReal.mul_rpow_of_nonneg _ _ hθ)
  have hlo := ENNReal.ofReal_le_ofReal (scaleKernelConstant_small (n := n) (r := q) hC hδ hL)
  have hhi := ENNReal.ofReal_le_ofReal (scaleKernelConstant_small (n := n) (r := q - 1) hC hδ hL)
  rw [ENNReal.ofReal_mul (scaleKernelConstant_nonneg (by norm_num))] at hlo hhi
  apply le_trans (mul_le_mul_right (show convolutionEnvelopeConstant n p q (C * δ ^ (-q)) B₂ Bₚ L ≤
    (ENNReal.ofReal (scaleKernelConstant n q q 1 0) * maximalLpConstant n p) * ENNReal.ofReal (C * δ) +
      ((cubeBallRatio n ^ (1 / 2 : ℝ) * ENNReal.ofReal (2 * (q + 1) / Real.log 2 + 4) ^
          (1 / 2 - 1 / p)) * squareMaximalLpConstant n p) *
        (ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) * Bₚ) +
      (cubeBallRatio n ^ (1 / 2 : ℝ) * squareMaximalLpConstant n p) * B₂ +
      (ENNReal.ofReal (scaleKernelConstant n q (q - 1) 1 0) * maximalLpConstant n p) * ENNReal.ofReal (C * δ) from ?_) _)
  · unfold combiningLogConstant
    conv_rhs => rw [mul_assoc]
    exact mul_le_mul_right (ennreal_four_linear_le _ _ _ _ _ _ _) _
  · unfold convolutionEnvelopeConstant
    apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact (mul_le_mul_left hlo _).trans_eq (by ring)
        · exact (mul_le_mul_left (mul_le_mul_right hc _) _).trans_eq (by ring)
      · apply le_of_eq
        ring
    · exact (mul_le_mul_left hhi _).trans_eq (by ring)

theorem combiningLogConstant_ne_top {n : ℕ} {p q : ℝ} (hp : 2 < p) :
    combiningLogConstant n p q ≠ ∞ := by
  have hp0 : 0 < p := by linarith
  have hθ : 0 ≤ 1 / 2 - 1 / p := by
    have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp.le
    linarith
  have hm : maximalLpConstant n p ≠ ∞ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hs : squareMaximalLpConstant n p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)) ENNReal.ofReal_ne_top)
  have hd : cubeBallRatio n ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (cubeBallRatio_lt_top n).ne
  have hk : ENNReal.ofReal (2 * (q + 1) / Real.log 2 + 4) ^ (1 / 2 - 1 / p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hθ ENNReal.ofReal_ne_top
  have ht : sharpLpConstant n p ≠ ∞ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
  exact ENNReal.mul_ne_top ht (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hd hk) hs⟩, ENNReal.mul_ne_top hd hs⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm⟩)

/-- The logarithmic combining-dilates estimate for a finite family of
dyadically scaled kernels. The constant depends only on dimension, the
Lebesgue exponent and the decay exponent; in particular not on `δ` or the
number of scales. -/
theorem combining_dyadic_kernels {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    {p q C δ : ℝ} (hp : 2 < p) (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖K i u‖ ≤ (C * δ ^ (-q)) * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hK' : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ (C * δ ^ (-q)) *
      (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) * ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (f i))
    (hfb : ∀ i, BddAbove (range fun x => ‖f i x‖))
    (hf2 : ∀ i, MemLp (f i) 2 volume) {B₂ Bₚ : ℝ≥0∞} (hB₂ : B₂ ≠ ∞)
    (h2 : ∀ i (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (convolveKernel (K i) g) 2 volume ≤ B₂ * eLpNorm g 2 volume)
    (hBₚ : ∀ i, eLpNorm (convolveKernel (K i) (f i)) (ENNReal.ofReal p) volume ≤
      Bₚ * eLpNorm (f i) (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => vectorNorm (fun i => convolveKernel (K i) (f i) x))
      (ENNReal.ofReal p) volume ≤
      (combiningLogConstant n p q *
        (ENNReal.ofReal (C * δ) + ENNReal.ofReal (1 + Real.log (1 / δ)) ^
          (1 / 2 - 1 / p) * Bₚ + B₂)) *
        eLpNorm (fun x => vectorNorm (fun i => f i x)) (ENNReal.ofReal p) volume := by
  have hq0 : 0 ≤ q := by linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨L, hL, hpow, hcard⟩ := exists_logarithmic_window hq0 hδ hδ1
  have h := combining_scale_family s K f hp hq (by positivity : 0 ≤ C * δ ^ (-q))
    hKd hK hK' hfm hfi hfb hf2 hB₂ h2 hBₚ hL
  exact h.trans (mul_le_mul_left
    (convolutionEnvelopeConstant_log_bound hp hq0 hC hδ hδ1 hpow hcard B₂ Bₚ) _)

end OAI.Analysis.Fourier.SquareFunction
