import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Dilation Monomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DilationMonomial

noncomputable section

/-! A polynomial with a single dilation weight has only the corresponding monomial when the dilation scalar has distinct natural powers. -/
universe u

theorem polynomial_eq_monomial_of_dilation
    {R : Type u} [Field R] (P : Polynomial R) (a : R) (g : ℕ)
    (hpow : Function.Injective (fun n : ℕ => a ^ n))
    (hP : P.comp (Polynomial.C a * Polynomial.X) = Polynomial.C (a ^ g) * P) :
    P = Polynomial.monomial g (P.coeff g) := by
  classical
  have hz (n : ℕ) (hn : n ≠ g) : P.coeff n = 0 := by
    by_contra hc
    have h := congrArg (fun Q : Polynomial R => Q.coeff n) hP
    rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at h
    exact hn (hpow (mul_left_cancel₀ hc (h.trans (mul_comm _ _))))
  apply Polynomial.ext
  intro n
  by_cases hn : n = g
  · subst n
    simp
  · simpa only [Polynomial.coeff_monomial, ite_eq_right (Ne.symm hn)] using hz n hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DilationMonomial
