import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketCartanRealization

/-! # Orthogonal Bracket Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketCompactness.Construction

noncomputable section

/-! Orthogonal bracket-preserving operators form a compact set in
finite dimension. These supply the compact factor in Cartan decomposition. -/

open Set

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def orthogonalBracketOperators (B : L →L[ℝ] L →L[ℝ] L) : Set (L →L[ℝ] L) :=
  {T | (∀ x y, T (B x y) = B (T x) (T y)) ∧ (∀ x y, inner ℝ (T x) (T y) = inner ℝ x y)}

omit [FiniteDimensional ℝ L] in
theorem orthogonalBracketOperators_isClosed (B : L →L[ℝ] L →L[ℝ] L) :
    IsClosed (orthogonalBracketOperators B) := by
  have hpres : IsClosed {T : L →L[ℝ] L | ∀ x y, T (B x y) = B (T x) (T y)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_eq (continuous_id.clm_apply continuous_const)
    exact (B.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      (continuous_id.clm_apply continuous_const)
  have hortho : IsClosed {T : L →L[ℝ] L | ∀ x y, inner ℝ (T x) (T y) = inner ℝ x y} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_eq ((continuous_id.clm_apply continuous_const).inner
      (continuous_id.clm_apply continuous_const)) continuous_const
  exact hpres.inter hortho

theorem orthogonalBracketOperators_isCompact (B : L →L[ℝ] L →L[ℝ] L) :
    IsCompact (orthogonalBracketOperators B) := by
  let : ProperSpace (L →L[ℝ] L) := FiniteDimensional.proper ℝ (L →L[ℝ] L)
  apply (isCompact_closedBall (0 : L →L[ℝ] L) 1).of_isClosed_subset
    (orthogonalBracketOperators_isClosed B)
  intro T hT
  change dist T 0 ≤ 1
  rw [dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound T (by norm_num)
  intro x
  have hs : ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hT.2 x x
  have hn := (sq_eq_sq₀ (norm_nonneg (T x)) (norm_nonneg x)).mp hs
  simp only [hn, one_mul, le_refl]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketCompactness.Construction
