import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Rat

/-! # Eventual Grid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid

section

/-! Rational polynomials are determined by their values at positive natural numbers. -/

theorem polynomial_eq_of_positive_nat_evals (P Q : Polynomial ℚ)
    (h : ∀ n : ℕ, 0 < n → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℚ)) := by
    intro m n he
    exact Nat.add_right_cancel (Nat.cast_injective he)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨n, rfl⟩
  exact h (n + 1) (Nat.succ_pos n)

end

/-! Polynomial identities on all sufficiently large integer pairs extend
to every integer pair. The threshold can be different in each direction. -/

theorem polynomial_eq_of_eventual_nat_evals (P Q : Polynomial ℚ) (B : ℕ)
    (h : ∀ n : ℕ, B ≤ n → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((B + n : ℕ) : ℚ)) := by
    intro m n he
    exact Nat.add_left_cancel (Nat.cast_injective he)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨n, rfl⟩
  exact h (B + n) (Nat.le_add_right B n)

theorem separately_polynomial_eq_of_eventual_grid
    (F G : ℤ → ℤ → ℚ)
    (hF₁ : ∀ b : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b)
    (hF₂ : ∀ a : ℤ, ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = F a b)
    (hG₁ : ∀ b : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = G a b)
    (hG₂ : ∀ a : ℤ, ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = G a b)
    (B C : ℕ)
    (hgrid : ∀ a b : ℕ, B ≤ a → C ≤ b → F a b = G a b)
    (a b : ℤ) : F a b = G a b := by
  have hnat (m : ℕ) (hm : B ≤ m) (b : ℤ) : F m b = G m b := by
    obtain ⟨P, hP⟩ := hF₂ m
    obtain ⟨Q, hQ⟩ := hG₂ m
    have he : P = Q := by
      apply polynomial_eq_of_eventual_nat_evals P Q C
      intro n hn
      simpa only [Int.cast_natCast] using
        (hP (n : ℤ)).trans ((hgrid m n hm hn).trans (hQ (n : ℤ)).symm)
    exact (hP b).symm.trans ((congrArg (fun R : Polynomial ℚ => R.eval (b : ℚ)) he).trans (hQ b))
  obtain ⟨P, hP⟩ := hF₁ b
  obtain ⟨Q, hQ⟩ := hG₁ b
  have he : P = Q := by
    apply polynomial_eq_of_eventual_nat_evals P Q B
    intro n hn
    simpa only [Int.cast_natCast] using
      (hP (n : ℤ)).trans ((hnat n hn b).trans (hQ (n : ℤ)).symm)
  exact (hP a).symm.trans ((congrArg (fun R : Polynomial ℚ => R.eval (a : ℚ)) he).trans (hQ a))

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
