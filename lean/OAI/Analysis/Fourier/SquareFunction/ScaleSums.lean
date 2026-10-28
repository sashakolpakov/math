import OAI.Analysis.Fourier.SquareFunction.LocalSquare

/-! Uniform finite geometric sums for the low and high scale ranges. -/

namespace OAI.Analysis.Fourier.SquareFunction

open scoped BigOperators

theorem finite_geometric_lower {s : Finset ℤ} {b : ℤ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hb : ∀ k ∈ s, k ≤ b) :
    ∑ k ∈ s, t ^ (b - k) ≤ (1 - t)⁻¹ := by
  classical
  have hinj : Set.InjOn (fun k : ℤ => (b - k).toNat) (s : Set ℤ) := by
    intro k hk l hl he
    have hek := Int.toNat_of_nonneg (sub_nonneg.mpr (hb k hk))
    have hel := Int.toNat_of_nonneg (sub_nonneg.mpr (hb l hl))
    have he' := congrArg (fun m : ℕ => (m : ℤ)) he
    rw [hek, hel] at he'
    omega
  have hs : ∑ k ∈ s, t ^ (b - k) = ∑ m ∈ s.image (fun k => (b - k).toNat), t ^ m := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hb k hk))]
  rw [hs]
  exact ((summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _
    (fun m _ => pow_nonneg ht0 m)).trans_eq (tsum_geometric_of_lt_one ht0 ht1)

theorem finite_geometric_upper {s : Finset ℤ} {b : ℤ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hb : ∀ k ∈ s, b ≤ k) :
    ∑ k ∈ s, t ^ (k - b) ≤ (1 - t)⁻¹ := by
  classical
  have hinj : Set.InjOn (fun k : ℤ => (k - b).toNat) (s : Set ℤ) := by
    intro k hk l hl he
    have hek := Int.toNat_of_nonneg (sub_nonneg.mpr (hb k hk))
    have hel := Int.toNat_of_nonneg (sub_nonneg.mpr (hb l hl))
    have he' := congrArg (fun m : ℕ => (m : ℤ)) he
    rw [hek, hel] at he'
    omega
  have hs : ∑ k ∈ s, t ^ (k - b) = ∑ m ∈ s.image (fun k => (k - b).toNat), t ^ m := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hb k hk))]
  rw [hs]
  exact ((summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _
    (fun m _ => pow_nonneg ht0 m)).trans_eq (tsum_geometric_of_lt_one ht0 ht1)

theorem low_scale_square_sum {s : Finset ℤ} {j L : ℤ}
    (hs : ∀ k ∈ s, k ≤ j - L) :
    ∑ k ∈ s, ((2 : ℝ) ^ (k - j)) ^ 2 ≤ (4 / 3 : ℝ) * ((2 : ℝ) ^ (-L)) ^ 2 := by
  have he (k : ℤ) : ((2 : ℝ) ^ (k - j)) ^ 2 =
      ((2 : ℝ) ^ (-L)) ^ 2 * (1 / 4 : ℝ) ^ ((j - L) - k) := by
    rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) by norm_num,
      ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (finite_geometric_lower (t := (1 / 4 : ℝ)) (by norm_num) (by norm_num) hs)
    (sq_nonneg ((2 : ℝ) ^ (-L)))
  simpa only [show (1 - (1 / 4 : ℝ))⁻¹ = 4 / 3 by norm_num, mul_comm] using h

theorem high_scale_square_sum {s : Finset ℤ} {j L : ℤ}
    (hs : ∀ k ∈ s, j + L ≤ k) :
    ∑ k ∈ s, ((2 : ℝ) ^ (-(k - j))) ^ 2 ≤ (4 / 3 : ℝ) * ((2 : ℝ) ^ (-L)) ^ 2 := by
  have he (k : ℤ) : ((2 : ℝ) ^ (-(k - j))) ^ 2 =
      ((2 : ℝ) ^ (-L)) ^ 2 * (1 / 4 : ℝ) ^ (k - (j + L)) := by
    rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) by norm_num,
      ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (finite_geometric_upper (t := (1 / 4 : ℝ)) (by norm_num) (by norm_num) hs)
    (sq_nonneg ((2 : ℝ) ^ (-L)))
  simpa only [show (1 - (1 / 4 : ℝ))⁻¹ = 4 / 3 by norm_num, mul_comm] using h

/-- A middle window has at most `2L` scales, independently of the finite
sequence of frequencies in which it is embedded. -/
theorem middle_window_card {s : Finset ℤ} {j L : ℤ} :
    (s.filter (fun k => j - L < k ∧ k < j + L)).card ≤ (2 * L).toNat := by
  classical
  have hsub : s.filter (fun k => j - L < k ∧ k < j + L) ⊆ Finset.Ioo (j - L) (j + L) := by
    intro k hk
    exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hk).2
  have h := Finset.card_le_card hsub
  rw [Int.card_Ioo] at h
  exact h.trans (Int.toNat_le_toNat (by omega))

/-- Every positive spatial radius has a dyadic reference scale with bounded
distortion. This avoids restricting the sharp argument to a particular grid. -/
theorem exists_dyadic_reference {r : ℝ} (hr : 0 < r) :
    ∃ j : ℤ, 1 / 2 < (2 : ℝ) ^ j * r ∧ (2 : ℝ) ^ j * r ≤ 1 := by
  obtain ⟨k, hklo, hkhi⟩ := exists_mem_Ico_zpow (inv_pos.mpr hr) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, ?_⟩
  · have h := (mul_lt_mul_iff_of_pos_right hr).mpr hkhi
    rw [inv_mul_cancel₀ hr.ne', zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at h
    nlinarith
  · have h := (mul_le_mul_iff_of_pos_right hr).mpr hklo
    rwa [inv_mul_cancel₀ hr.ne'] at h

theorem dyadic_scale_identity (k j : ℤ) (r : ℝ) :
    (2 : ℝ) ^ k * r = (2 : ℝ) ^ (k - j) * ((2 : ℝ) ^ j * r) := by
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

theorem reference_scale_upper {j : ℤ} {r : ℝ}
    (hj : (2 : ℝ) ^ j * r ≤ 1) (k : ℤ) :
    (2 : ℝ) ^ k * r ≤ (2 : ℝ) ^ (k - j) := by
  rw [dyadic_scale_identity k j r]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hj
    (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (k - j))

theorem reference_scale_unit {k j : ℤ} {r : ℝ}
    (hj : (2 : ℝ) ^ j * r ≤ 1) (hk : k ≤ j) :
    (2 : ℝ) ^ k * r ≤ 1 := by
  apply (reference_scale_upper hj k).trans
  simpa only [zpow_zero] using zpow_le_zpow_right₀
    (by norm_num : (1 : ℝ) ≤ 2) (show k - j ≤ 0 by omega)

theorem reference_tail_inverse {j : ℤ} {r : ℝ}
    (hj : 1 / 2 < (2 : ℝ) ^ j * r) (k : ℤ) :
    ((2 : ℝ) ^ k * (2 * r))⁻¹ ≤ (2 : ℝ) ^ (-(k - j)) := by
  have hpos : 0 < (2 : ℝ) ^ (k - j) := zpow_pos (by norm_num) _
  have h : (2 : ℝ) ^ (k - j) ≤ (2 : ℝ) ^ k * (2 * r) := by
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * ((2 : ℝ) ^ j * r) by linarith) hpos.le
    calc
      _ ≤ (2 : ℝ) ^ (k - j) * (2 * ((2 : ℝ) ^ j * r)) := by simpa only [mul_one] using hh
      _ = _ := by rw [dyadic_scale_identity k j (2 * r)]; ring
  rw [zpow_neg]
  exact inv_anti₀ hpos h

end OAI.Analysis.Fourier.SquareFunction
