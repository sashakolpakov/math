import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingNilpotentPolynomials

/-! # Nilpotent Exponential Unipotent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialUnipotent.Construction

noncomputable section

/-! The analytic exponential of a nilpotent element is unipotent. -/

open NormedSpace

theorem nilpotent_exponential_sub_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : A) (hX : IsNilpotent X) : IsNilpotent (exp X - 1) := by
  obtain ⟨m, hm⟩ := hX
  rw [NilpotentExponentialPolynomial.Construction.exp_eq_finite_sum_of_pow_eq_zero X (m + 1) (pow_eq_zero_of_le (by omega) hm),
    Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, add_sub_cancel_right]
  apply Commute.isNilpotent_sum
  · intro n _
    exact (IsNilpotent.pow_of_pos ⟨m, hm⟩ (Nat.succ_ne_zero n)).smul _
  · intro n k _ _
    exact ((Commute.pow_pow_self X (n + 1) (k + 1)).smul_left _).smul_right _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialUnipotent.Construction
