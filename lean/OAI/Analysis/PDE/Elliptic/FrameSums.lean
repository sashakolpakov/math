import OAI.Analysis.PDE.Elliptic.RankOneFrame

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem rankOne_quarter_pair (u v : E) (eps a : ℝ) :
    ((eps + a) / 4) • rankOne ℝ (u + v) (u + v) +
      ((eps - a) / 4) • rankOne ℝ (u - v) (u - v) =
    (eps / 2) • rankOne ℝ u u + (eps / 2) • rankOne ℝ v v +
      (1 / 2 : ℝ) • (a • rankOne ℝ u v) + (1 / 2 : ℝ) • (a • rankOne ℝ v u) := by
  ext x
  simp only [add_apply, smul_apply,
    rankOne_apply, inner_add_left, inner_sub_left]
  module

omit [FiniteDimensional ℝ E] in
theorem symmetric_rankOne_sum_transpose {I : Type*} [Fintype I]
    (b : I → E) (a : I → I → ℝ) (ha : ∀ i j, a i j = a j i) :
    (∑ j, ∑ i, a i j • rankOne ℝ (b j) (b i)) =
      ∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [ha j i]

omit [FiniteDimensional ℝ E] in
/-- The signed-pair decomposition of a symmetric array differs from
its rank-one expansion by an explicit scalar identity. -/
theorem signed_pair_sum_eq {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (a : I → I → ℝ) (ha : ∀ i j, a i j = a j i)
    (eps : ℝ) :
    (∑ j, ∑ i, (((eps + a i j) / 4) • rankOne ℝ (b i + b j) (b i + b j) +
      ((eps - a i j) / 4) • rankOne ℝ (b i - b j) (b i - b j))) =
      (eps * Fintype.card I) • ContinuousLinearMap.id ℝ E +
        ∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j) := by
  have hdiag1 : (∑ _j : I, ∑ i : I, rankOne ℝ (b i) (b i)) =
      (Fintype.card I : ℝ) • ContinuousLinearMap.id ℝ E := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      b.sum_rankOne_eq_id]
  have hdiag2 : (∑ j : I, ∑ _i : I, rankOne ℝ (b j) (b j)) =
      (Fintype.card I : ℝ) • ContinuousLinearMap.id ℝ E := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Finset.smul_sum, b.sum_rankOne_eq_id]
  simp_rw [rankOne_quarter_pair, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hdiag1, hdiag2, symmetric_rankOne_sum_transpose b a ha]
  module

end OAI.Analysis.PDE.Elliptic
