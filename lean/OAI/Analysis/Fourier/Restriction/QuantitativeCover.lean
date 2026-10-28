import OAI.Analysis.Fourier.Restriction.Branching

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Quantitative sparse covering: at most `3*N*M^(1/N)` color families,
polynomially separated centers, and radii bounded by an explicit
`M^(C^N)`-type expression. This is the geometric epsilon-removal lemma. -/
theorem finite_sparse_cover_quantitative {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (E : Finset X) (M N D : ℕ) (hM : 1 ≤ M) (hcard : E.card ≤ M)
    (hN : 0 < N) (hD : 0 < D) :
    ∃ K : ℕ, ∃ T : Fin N → Finset X, ∃ c : Fin N → X → Fin (K + 1),
      ((N * (K + 1) : ℕ) : ℝ) ≤ 3 * N * (M : ℝ) ^ (1 / (N : ℝ)) ∧
      (∀ j, T j ⊆ E) ∧
      (∀ j, ∀ z ∈ T j, ∀ w ∈ T j, z ≠ w → c j z = c j w →
        (4 * sparseScale M D j) ^ D * (M : ℝ) ^ D ≤ dist z w) ∧
      (∀ x ∈ E, ∃ j : Fin N, ∃ y ∈ T j, dist x y < 4 * sparseScale M D j) ∧
      ∀ j : Fin N, 4 * sparseScale M D j ≤
        4 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N) := by
  obtain ⟨K, hK, hMK, hcolor⟩ := exists_sparse_branching M N hM hN
  obtain ⟨T, c, hTE, hsep, hcover⟩ := finite_sparse_cover E K N hK hN (hcard.trans hMK)
    (sparseScale M D)
    (fun j ↦ (by norm_num : (0 : ℝ) < 4).trans_le (sparseScale_ge_four M D j))
    (fun j _ ↦ sparseScale_step M D j hD)
  refine ⟨K, T, c, ?_, hTE, ?_, hcover, ?_⟩
  · have H := mul_le_mul_of_nonneg_left hcolor (Nat.cast_nonneg (α := ℝ) N)
    simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using H
  · intro j z hz w hw hzw hc
    exact (sparseScale_separation M D j).trans (hsep j z hz w hw hzw hc)
  · intro j
    exact mul_le_mul_of_nonneg_left (sparseScale_mono M D (Nat.le_of_lt j.isLt)) (by norm_num)

end OAI.Analysis.Fourier.Restriction
