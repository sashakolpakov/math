import OAI.Analysis.Fourier.BochnerRiesz.SymbolPartition

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem sum_geometric_shift_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J N : ℕ) :
    ∑ j ∈ Finset.range N, q ^ (J + j) ≤ (1 - q)⁻¹ := by
  have hpow : ∀ j : ℕ, q ^ j ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      nlinarith [pow_nonneg hq0 j]
  have hgeom : ∀ k : ℕ, (1 - q) * (∑ j ∈ Finset.range k, q ^ j) = 1 - q ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  have hb : (∑ j ∈ Finset.range N, q ^ j) ≤ (1 - q)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith [hgeom N, pow_nonneg hq0 N]
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro j hj
  rw [pow_add]
  nlinarith [pow_nonneg hq0 j, hpow J]

theorem dyadic_rpow_product {δ σ : ℝ} (j : ℕ) :
    ((2 : ℝ) ^ j) ^ (-δ) * ((2 : ℝ) ^ j) ^ σ = ((2 : ℝ) ^ (σ - δ)) ^ j := by
  rw [← Real.rpow_add (by positivity), ← Real.rpow_natCast_mul (by norm_num),
    show (j : ℝ) * (-δ + σ) = (σ - δ) * j by ring,
    Real.rpow_mul_natCast (by norm_num)]

theorem sum_dyadic_rpow_product_le {δ σ : ℝ} (h : σ < δ) (J N : ℕ) :
    ∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-δ) * ((2 : ℝ) ^ (J + j)) ^ σ ≤
      (1 - (2 : ℝ) ^ (σ - δ))⁻¹ := by
  simp_rw [dyadic_rpow_product]
  exact sum_geometric_shift_le (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)) J N

theorem dyadic_rpow_sum_constant_pos {δ σ : ℝ} (h : σ < δ) :
    0 < (1 - (2 : ℝ) ^ (σ - δ))⁻¹ :=
  inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

end OAI.Analysis.Fourier.BochnerRiesz
