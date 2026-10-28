import OAI.Analysis.Fourier.Restriction.Sparse.Kernel

open _root_.MeasureTheory Set
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem separated_decay_bound {a P D R N d : ℝ}
    (ha : 0 < a) (hP : P ≤ D * a) (hD : 1 ≤ D * a)
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hsep : R ^ D * N ^ D ≤ d) :
    R ^ P * (1 + d) ^ (-a) ≤ N⁻¹ := by
  have hR0 : 0 < R := by linarith
  have hN0 : 0 < N := by linarith
  have hd : 0 < d := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hR0 _) (Real.rpow_pos_of_pos hN0 _)) hsep
  have hden : R ^ P * N ≤ (1 + d) ^ a := by
    calc
      _ ≤ R ^ (D * a) * N ^ (D * a) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le hR hP
        · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hD
        · exact hN0.le
        · positivity
      _ = (R ^ D * N ^ D) ^ a := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR0.le,
          ← Real.rpow_mul hN0.le]
      _ ≤ (1 + d) ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
  rw [Real.rpow_neg (by linarith : 0 ≤ 1 + d)]
  rw [← div_eq_mul_inv, ← one_div N,
    div_le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < 1 + d) a) hN0, one_mul]
  exact hden

theorem sparse_dimension_decay {n : ℕ} (hn : 2 ≤ n) {R N d : ℝ}
    (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hsep : R ^ ((16 : ℝ) * n) * N ^ ((16 : ℝ) * n) ≤ d) :
    (R ^ n * R ^ (((n : ℝ) - 1) / 2)) ^ 2 *
      (1 + d) ^ (-((n : ℝ) - 1) / 2) ≤ N⁻¹ := by
  let a : ℝ := ((n : ℝ) - 1) / 2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; linarith
  have hR0 : 0 < R := by linarith
  have hsq : (R ^ n * R ^ a) ^ 2 = R ^ (2 * ((n : ℝ) + a)) := by
    rw [← Real.rpow_natCast R n, ← Real.rpow_add hR0, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hR0.le]
    congr 1
    ring
  simp only [neg_div]
  change (R ^ n * R ^ a) ^ 2 * (1 + d) ^ (-a) ≤ _
  rw [hsq]
  apply separated_decay_bound ha (D := 16 * n) _ _ hR hN hsep
  · dsimp [a]
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · dsimp [a]
    nlinarith [sq_nonneg ((n : ℝ) - 2)]

end OAI.Analysis.Fourier.Restriction
