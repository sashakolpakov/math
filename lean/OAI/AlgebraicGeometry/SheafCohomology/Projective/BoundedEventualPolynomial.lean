import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Bounded Eventual Polynomial -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial

/-! Eventual polynomial descriptions with an explicit degree bound. -/

def EventuallyPolynomialOfDegree (f : ℕ → ℚ) (d : ℕ) : Prop :=
  ∃ P : Polynomial ℚ, P.natDegree ≤ d ∧ ∃ b : ℕ, ∀ n : ℕ, b ≤ n → f n = P.eval (n : ℚ)

theorem EventuallyPolynomialOfDegree.eventuallyPolynomial {f : ℕ → ℚ} {d : ℕ}
    (h : EventuallyPolynomialOfDegree f d) : EventualPolynomial.EventuallyPolynomial f := by
  obtain ⟨P, _, b, hb⟩ := h
  exact ⟨P, b, hb⟩

theorem eventuallyPolynomialOfDegree_zero (d : ℕ) :
    EventuallyPolynomialOfDegree (fun _ => 0) d :=
  ⟨0, by simp, 0, fun _ _ => Polynomial.eval_zero.symm⟩

theorem EventuallyPolynomialOfDegree.add {f g : ℕ → ℚ} {d : ℕ}
    (hf : EventuallyPolynomialOfDegree f d) (hg : EventuallyPolynomialOfDegree g d) :
    EventuallyPolynomialOfDegree (fun n => f n + g n) d := by
  obtain ⟨P, hP, p, hp⟩ := hf
  obtain ⟨Q, hQ, q, hq⟩ := hg
  refine ⟨P + Q, (Polynomial.natDegree_add_le _ _).trans (max_le hP hQ),
    max p q, fun n hn => ?_⟩
  change f n + g n = (P + Q).eval (n : ℚ)
  rw [hp n ((le_max_left p q).trans hn), hq n ((le_max_right p q).trans hn),
    Polynomial.eval_add]

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial
