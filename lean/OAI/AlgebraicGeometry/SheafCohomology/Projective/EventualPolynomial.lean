import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Cast.CharZero

/-! # Eventual Polynomial -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial

/-! Polynomial descriptions of rational sequences in all sufficiently large degrees. -/

def EventuallyPolynomial (f : ℕ → ℚ) : Prop :=
  ∃ P : Polynomial ℚ, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → f n = P.eval (n : ℚ)

theorem eventuallyPolynomial_zero : EventuallyPolynomial (fun _ => 0) :=
  ⟨0, 0, fun _ _ => (Polynomial.eval_zero).symm⟩

theorem EventuallyPolynomial.add {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n + g n) := by
  obtain ⟨P, p, hp⟩ := hf
  obtain ⟨Q, q, hq⟩ := hg
  refine ⟨P + Q, max p q, fun n hn => ?_⟩
  change f n + g n = (P + Q).eval (n : ℚ)
  rw [hp n ((le_max_left p q).trans hn), hq n ((le_max_right p q).trans hn),
    Polynomial.eval_add]

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial
