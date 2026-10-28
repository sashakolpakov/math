import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid

/-! # Integer Step -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerStep

/-! A rational polynomial constant on the positive multiples of a nonzero
integer has the same value at zero and one. -/

theorem polynomial_eval_one_of_constant_integer_multiples
    (P : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0)
    (h : ∀ n : ℕ, 0 < n → P.eval ((c : ℚ) * (n : ℚ)) = P.eval 0) :
    P.eval 1 = P.eval 0 := by
  have he : P.comp (Polynomial.C (c : ℚ) * Polynomial.X) = Polynomial.C (P.eval 0) := by
    apply EventualGrid.polynomial_eq_of_positive_nat_evals
    intro n hn
    simpa only [Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using h n hn
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hv := congrArg (fun Q : Polynomial ℚ => Q.eval (c : ℚ)⁻¹) he
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_inv_cancel₀ hc'] using hv

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerStep
