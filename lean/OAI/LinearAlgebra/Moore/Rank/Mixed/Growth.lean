import OAI.LinearAlgebra.Moore.Rank.Mixed.Binomial
import OAI.LinearAlgebra.Moore.MooreRankGrowth

noncomputable section
namespace OAI.LinearAlgebra.Moore

open scoped ComplexOrder

theorem coefficient_eq_zero_of_power_bound {c C : ℝ} {j r : ℕ}
    (hc : 0 ≤ c) (hrj : r < j)
    (hbound : ∀ t : ℝ, 1 ≤ t → c * t ^ j ≤ C * t ^ r) : c = 0 := by
  by_contra hn
  have hc0 : 0 < c := lt_of_le_of_ne hc (Ne.symm hn)
  let t : ℝ := max 1 ((C + 1) / c)
  have ht : 1 ≤ t := le_max_left _ _
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htc : C + 1 ≤ t * c := by
    exact (div_le_iff₀ hc0).mp (le_max_right _ _)
  have hp : t ^ (r + 1) ≤ t ^ j := pow_le_pow_right₀ ht (by omega)
  have hle := (mul_le_mul_of_nonneg_left hp hc).trans (hbound t ht)
  rw [pow_succ] at hle
  have hle' : (c * t) * t ^ r ≤ C * t ^ r := by nlinarith [hle]
  have hct : c * t ≤ C := (mul_le_mul_iff_left₀ (pow_pos ht0 r)).mp (by
    simpa only [mul_comm] using hle')
  nlinarith

theorem mixedMoore_eq_zero_of_rank_and_nonneg {m r j : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hB : (complexify B).PosSemidef) (hD : (complexify D).PosSemidef)
    (hr : QuaternionRankLE r B) (hrj : r < j) (hjm : j ≤ m)
    (hnonneg : ∀ k ≤ m, 0 ≤ mixedMoore m (fun i => if i.val < k then B else D)) :
    mixedMoore m (fun i => if i.val < j then B else D) = 0 := by
  obtain ⟨C, hC, hgrowth⟩ := mooreDet_psd_rank_growth B D hB hD hr (by omega)
  let c : ℝ := (m.choose j : ℝ) * mixedMoore m (fun i => if i.val < j then B else D)
  have hcn : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (hnonneg j hjm)
  have hc : c = 0 := coefficient_eq_zero_of_power_bound hcn hrj (by
    intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have he := mooreDet_linear_combination_mixed B D 1 t
    simp only [one_smul, one_pow, mul_one] at he
    have hterm : c * t ^ j ≤ mooreDet m (D + t • B) := by
      rw [he]
      have hj : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
      have hn (k : ℕ) (hk : k ∈ Finset.range (m+1)) :
          0 ≤ (m.choose k : ℝ) * t ^ k * mixedMoore m (fun i => if i.val < k then B else D) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0 _))
          (hnonneg k (by simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      have hs := Finset.single_le_sum hn hj
      dsimp [c]
      nlinarith [hs]
    exact hterm.trans (hgrowth t ht))
  have hjpos : (0 : ℝ) < m.choose j := by exact_mod_cast Nat.choose_pos hjm
  exact (mul_eq_zero.mp hc).resolve_left hjpos.ne'

end OAI.LinearAlgebra.Moore
