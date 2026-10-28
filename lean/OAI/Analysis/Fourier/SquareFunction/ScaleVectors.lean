import OAI.Analysis.Fourier.SquareFunction.ScaleSums

/-! Geometric scale gains in the actual finite Hilbert-space vector norm. -/

namespace OAI.Analysis.Fourier.SquareFunction

theorem sum_mask_over_subtype {s : Finset ℤ} (P : ℤ → Prop) [DecidablePred P]
    (F : ℤ → ℝ) : (∑ i : s, if P i.val then F i.val else 0) = ∑ k ∈ s.filter P, F k := by
  classical
  rw [Finset.sum_filter]
  exact Finset.sum_attach s (fun k => if P k then F k else 0)

theorem low_scale_vector_le {H : Type*} [SeminormedAddCommGroup H]
    (s : Finset ℤ) (v : s → H) {j L : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ (if i.val ≤ j - L then (2 : ℝ) ^ (i.val - j) else 0) * C) :
    vectorNorm v ≤ Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) * C := by
  classical
  let a : s → ℝ := fun i => if i.val ≤ j - L then (2 : ℝ) ^ (i.val - j) else 0
  have ha : ∀ i, 0 ≤ a i := by intro i; dsimp [a]; split_ifs <;> positivity
  have hsum : (∑ i : s, a i ^ 2) ≤ (4 / 3 : ℝ) * ((2 : ℝ) ^ (-L)) ^ 2 := by
    have he : (∑ i : s, a i ^ 2) = ∑ k ∈ s.filter (fun k => k ≤ j - L), ((2 : ℝ) ^ (k - j)) ^ 2 := by
      calc
        _ = ∑ i : s, if i.val ≤ j - L then ((2 : ℝ) ^ (i.val - j)) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [a]
          split_ifs <;> simp
        _ = _ := sum_mask_over_subtype (s := s) (fun k => k ≤ j - L)
          (fun k => ((2 : ℝ) ^ (k - j)) ^ 2)
    rw [he]
    exact low_scale_square_sum (fun k hk => (Finset.mem_filter.mp hk).2)
  have h := (vectorNorm_le_weighted v a hC ha hv).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsum) hC)
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
    Real.sqrt_sq (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-L)))] using h

theorem high_scale_vector_le {H : Type*} [SeminormedAddCommGroup H]
    (s : Finset ℤ) (v : s → H) {j L : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ (if j + L ≤ i.val then (2 : ℝ) ^ (-(i.val - j)) else 0) * C) :
    vectorNorm v ≤ Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) * C := by
  classical
  let a : s → ℝ := fun i => if j + L ≤ i.val then (2 : ℝ) ^ (-(i.val - j)) else 0
  have ha : ∀ i, 0 ≤ a i := by intro i; dsimp [a]; split_ifs <;> positivity
  have hsum : (∑ i : s, a i ^ 2) ≤ (4 / 3 : ℝ) * ((2 : ℝ) ^ (-L)) ^ 2 := by
    have he : (∑ i : s, a i ^ 2) = ∑ k ∈ s.filter (fun k => j + L ≤ k), ((2 : ℝ) ^ (-(k - j))) ^ 2 := by
      calc
        _ = ∑ i : s, if j + L ≤ i.val then ((2 : ℝ) ^ (-(i.val - j))) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [a]
          split_ifs <;> simp
        _ = _ := sum_mask_over_subtype (s := s) (fun k => j + L ≤ k)
          (fun k => ((2 : ℝ) ^ (-(k - j))) ^ 2)
    rw [he]
    exact high_scale_square_sum (fun k hk => (Finset.mem_filter.mp hk).2)
  have h := (vectorNorm_le_weighted v a hC ha hv).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsum) hC)
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
    Real.sqrt_sq (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-L)))] using h

end OAI.Analysis.Fourier.SquareFunction
