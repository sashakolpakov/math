import Mathlib.Tactic

/-! # Small Positive Parameter -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmallPositiveParameter

/-! A genuine positive parameter simultaneously fits two local radii and a prescribed quantitative point-error bound. -/

theorem exists_small_positive_parameter (A B C D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ A ∧ ε ≤ B ∧ D * ε < C := by
  have ht : 0 < min 1 (min A (min B (C / D))) :=
    lt_min zero_lt_one (lt_min hA (lt_min hB (div_pos hC hD)))
  obtain ⟨ε, hε, he⟩ := exists_between ht
  have he1 : ε < 1 := he.trans_le (min_le_left _ _)
  have heA : ε < A := (he.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have heB : ε < B := ((he.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have heD : ε < C / D := ((he.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  refine ⟨ε, hε, he1.le, heA.le, heB.le, ?_⟩
  simpa only [mul_comm ε D] using (lt_div_iff₀ hD).mp heD

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmallPositiveParameter
