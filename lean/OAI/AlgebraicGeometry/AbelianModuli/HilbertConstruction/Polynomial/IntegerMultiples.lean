import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid

/-! # Integer Multiples -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerMultiples

/-! Positive multiples of any nonzero integer determine a rational
polynomial, including its values away from that arithmetic progression. -/

theorem polynomial_eq_of_positive_integer_multiple_evals
    (P Q : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0)
    (h : ∀ n : ℕ, 0 < n → P.eval ((c : ℚ) * (n : ℚ)) = Q.eval ((c : ℚ) * (n : ℚ))) :
    P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hc' : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hi : Function.Injective (fun n : ℕ => (c : ℚ) * ((n + 1 : ℕ) : ℚ)) := by
    intro n m hnm
    exact Nat.add_right_cancel (Nat.cast_injective (mul_left_cancel₀ hc' hnm))
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro x ⟨n, rfl⟩
  exact h (n + 1) (Nat.succ_pos n)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerMultiples
