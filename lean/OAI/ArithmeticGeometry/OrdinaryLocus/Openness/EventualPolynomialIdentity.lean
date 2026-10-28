import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Order.Interval.Set.Infinite

/-! # Eventual Polynomial Identity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EventualPolynomialIdentity.Construction

/-! Eventual equality on the natural numbers determines a rational polynomial. -/

theorem polynomial_eq_of_eventually_nat_eval_eq (P Q : Polynomial ℚ)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Set.Infinite ((fun n : ℕ => (n : ℚ)) '' Set.Ici b) :=
    (Set.Ici_infinite b).image Nat.cast_injective.injOn
  apply hi.mono
  rintro _ ⟨n, hn, rfl⟩
  exact h n hn

theorem polynomial_comp_mul_of_eventually_eval (P Q : Polynomial ℚ)
    (a b : ℕ) (h : ∀ n : ℕ, b ≤ n → Q.eval (n : ℚ) = P.eval ((n * a : ℕ) : ℚ)) :
    Q = P.comp (Polynomial.X * Polynomial.C (a : ℚ)) := by
  apply polynomial_eq_of_eventually_nat_eval_eq _ _ b
  intro n hn
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_mul] using h n hn

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EventualPolynomialIdentity.Construction
