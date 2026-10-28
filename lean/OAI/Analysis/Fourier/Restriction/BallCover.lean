import OAI.Analysis.Fourier.Restriction.QuantitativeCover

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparseScale_separation_five (M D j : ℕ) (hM : 1 ≤ M) :
    (5 * sparseScale M D j) ^ D * (M : ℝ) ^ D ≤ sparseScale M D (j + 1) := by
  have hbase := sparseScale_base_le M D j
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlarge : 8 ≤ sparseScale M D j := by linarith
  have hsmall : (M : ℝ) ≤ sparseScale M D j := by linarith
  have hsq : 5 * sparseScale M D j ≤ sparseScale M D j ^ 2 := by nlinarith
  calc
    _ ≤ (sparseScale M D j ^ 2) ^ D * sparseScale M D j ^ D := by gcongr
    _ = sparseScale M D j ^ (3 * D) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ sparseScale M D j ^ (3 * D + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := (sparseScale_succ M D j).symm

/-- The geometric epsilon-removal cover, thickened to the union of
unit balls around the original finite set of centers. -/
theorem unit_ball_sparse_cover {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (E : Finset X) (M N D : ℕ) (hM : 1 ≤ M) (hcard : E.card ≤ M)
    (hN : 0 < N) (hD : 0 < D) :
    ∃ K : ℕ, ∃ T : Fin N → Finset X, ∃ c : Fin N → X → Fin (K + 1),
      ((N * (K + 1) : ℕ) : ℝ) ≤ 3 * N * (M : ℝ) ^ (1 / (N : ℝ)) ∧
      (∀ j, T j ⊆ E) ∧
      (∀ j, ∀ z ∈ T j, ∀ w ∈ T j, z ≠ w → c j z = c j w →
        (5 * sparseScale M D j) ^ D * (M : ℝ) ^ D ≤ dist z w) ∧
      (∀ x, (∃ e ∈ E, dist x e < 1) →
        ∃ j : Fin N, ∃ y ∈ T j, dist x y < 5 * sparseScale M D j) ∧
      ∀ j : Fin N, 5 * sparseScale M D j ≤
        5 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N) := by
  obtain ⟨K, hK, hMK, hcolor⟩ := exists_sparse_branching M N hM hN
  obtain ⟨T, c, hTE, hsep, hcover⟩ := finite_sparse_cover E K N hK hN (hcard.trans hMK)
    (sparseScale M D)
    (fun j ↦ (by norm_num : (0 : ℝ) < 4).trans_le (sparseScale_ge_four M D j))
    (fun j _ ↦ sparseScale_step M D j hD)
  refine ⟨K, T, c, ?_, hTE, ?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left hcolor (Nat.cast_nonneg (α := ℝ) N)
    simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using H
  · intro j z hz w hw hzw hc
    exact (sparseScale_separation_five M D j hM).trans (hsep j z hz w hw hzw hc)
  · intro x hx
    obtain ⟨e, he, hxe⟩ := hx
    obtain ⟨j, y, hy, hey⟩ := hcover e he
    refine ⟨j, y, hy, ?_⟩
    have hr := sparseScale_ge_four M D j
    have htri := dist_triangle x e y
    linarith
  · intro j
    exact mul_le_mul_of_nonneg_left (sparseScale_mono M D (Nat.le_of_lt j.isLt)) (by norm_num)

end OAI.Analysis.Fourier.Restriction
