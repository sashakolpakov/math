import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid

/-! # Separate Polynomial Monomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatePolynomialMonomial

/-! A separately polynomial function on two integer variables is determined
by its values on the positive integer grid. -/

theorem separately_polynomial_monomial_of_positive_grid
    (F : ℤ → ℤ → ℚ) (d : ℕ) (c : ℚ)
    (hfirst : ∀ b : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b)
    (hsecond : ∀ a : ℤ, ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = F a b)
    (hpos : ∀ a b : ℕ, 0 < a → 0 < b → F a b = c * (a : ℚ) ^ d * (b : ℚ) ^ d)
    (a b : ℤ) : F a b = c * (a : ℚ) ^ d * (b : ℚ) ^ d := by
  have hnat (m : ℕ) (hm : 0 < m) (b : ℤ) :
      F m b = c * (m : ℚ) ^ d * (b : ℚ) ^ d := by
    obtain ⟨P, hP⟩ := hsecond m
    have he : P = Polynomial.monomial d (c * (m : ℚ) ^ d) := by
      apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
      intro n hn
      have hv := hP (n : ℤ)
      rw [Int.cast_natCast] at hv
      rw [hv, hpos m n hm hn, Polynomial.eval_monomial]
    rw [← hP b, he, Polynomial.eval_monomial]
  obtain ⟨P, hP⟩ := hfirst b
  have he : P = Polynomial.monomial d (c * (b : ℚ) ^ d) := by
    apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
    intro n hn
    have hv := hP (n : ℤ)
    rw [Int.cast_natCast] at hv
    rw [hv, hnat n hn b, Polynomial.eval_monomial]
    ring
  rw [← hP a, he, Polynomial.eval_monomial]
  ring

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatePolynomialMonomial
