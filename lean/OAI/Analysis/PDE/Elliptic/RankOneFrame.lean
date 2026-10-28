import OAI.Analysis.PDE.Elliptic.HessianTrace

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem rankOne_signed_pair (u v : E) (a b : ℝ) :
    ((a + b) / 2) • rankOne ℝ (u + v) (u + v) +
      ((a - b) / 2) • rankOne ℝ (u - v) (u - v) =
    a • rankOne ℝ u u + a • rankOne ℝ v v +
      b • rankOne ℝ u v + b • rankOne ℝ v u := by
  ext x
  simp only [add_apply, smul_apply,
    rankOne_apply, inner_add_left, inner_sub_left]
  module

omit [FiniteDimensional ℝ E] in
theorem rankOne_signed_pair_sum (u v : E) :
    rankOne ℝ (u + v) (u + v) + rankOne ℝ (u - v) (u - v) =
      (2 : ℝ) • rankOne ℝ u u + (2 : ℝ) • rankOne ℝ v v := by
  simpa only [add_zero, sub_zero, div_self (by norm_num : (2 : ℝ) ≠ 0),
    one_smul, zero_smul, add_zero] using rankOne_signed_pair u v 2 0

omit [FiniteDimensional ℝ E] in
theorem operator_rankOne_basis {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (A : E →L[ℝ] E) :
    A = ∑ j, rankOne ℝ (A (b j)) (b j) := by
  ext x
  simp only [sum_apply, rankOne_apply]
  calc
    A x = A (∑ j, inner ℝ (b j) x • b j) := by rw [b.sum_repr']
    _ = ∑ j, inner ℝ (b j) x • A (b j) := by simp only [map_sum, map_smul]

omit [FiniteDimensional ℝ E] in
theorem operator_rankOne_double_basis {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (A : E →L[ℝ] E) :
    A = ∑ j, ∑ i, inner ℝ (b i) (A (b j)) • rankOne ℝ (b i) (b j) := by
  ext x
  simp only [sum_apply, smul_apply, rankOne_apply]
  calc
    A x = ∑ j, inner ℝ (b j) x • A (b j) := by
      have h := congrArg (fun T : E →L[ℝ] E ↦ T x) (operator_rankOne_basis b A)
      simpa only [sum_apply, rankOne_apply] using h
    _ = ∑ j, ∑ i, inner ℝ (b i) (A (b j)) • (inner ℝ (b j) x • b i) := by
      apply Finset.sum_congr rfl
      intro j _
      conv_lhs => rw [← b.sum_repr' (A (b j))]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, smul_smul, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- The sum of the rank-one operators in a full signed basis frame is
a scalar identity, independent of the chosen orthonormal basis. -/
theorem signed_basis_frame_sum {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) :
    (∑ i, rankOne ℝ (b i) (b i)) +
      ∑ i, ∑ j, (rankOne ℝ (b i + b j) (b i + b j) +
        rankOne ℝ (b i - b j) (b i - b j)) =
      (1 + 4 * (Fintype.card I : ℝ)) • ContinuousLinearMap.id ℝ E := by
  simp_rw [rankOne_signed_pair_sum, Finset.sum_add_distrib]
  have hleft : (∑ i : I, ∑ _j : I, (2 : ℝ) • rankOne ℝ (b i) (b i)) =
      (Fintype.card I : ℝ) • ((2 : ℝ) • ∑ i, rankOne ℝ (b i) (b i)) := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Finset.smul_sum]
  have hright : (∑ _i : I, ∑ j : I, (2 : ℝ) • rankOne ℝ (b j) (b j)) =
      (Fintype.card I : ℝ) • ((2 : ℝ) • ∑ j, rankOne ℝ (b j) (b j)) := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Finset.smul_sum]
  rw [hleft, hright, b.sum_rankOne_eq_id]
  module

end OAI.Analysis.PDE.Elliptic
