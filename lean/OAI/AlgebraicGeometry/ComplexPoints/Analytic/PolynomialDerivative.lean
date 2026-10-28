import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialImplicit
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Polynomial Derivative -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative

/-!
# Analytic derivatives are the formal polynomial partial derivatives

This identifies the analytic derivative used by the implicit function theorem
with the evaluated algebraic Jacobian, in ordinary complex coordinates.
-/

open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem differentiable_polynomial_eval (p : MvPolynomial ι ℂ) :
    Differentiable ℂ (fun x : ι → ℂ => MvPolynomial.eval x p) :=
  (PolynomialImplicit.contDiff_polynomial_eval p 1).differentiable_one

/-- Each column of the analytic derivative is the corresponding evaluated
formal partial derivative. -/
theorem fderiv_polynomial_eval_single (p : MvPolynomial ι ℂ)
    (x : ι → ℂ) (i : ι) :
    fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x (Pi.single i 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add]
      rw [fderiv_fun_add (differentiable_polynomial_eval p x)
        (differentiable_polynomial_eval q x)]
      change
        fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x (Pi.single i 1) +
        fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y q) x (Pi.single i 1) = _
      rw [hp, hq]
  | mul_X p j hp =>
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [fderiv_fun_mul (differentiable_polynomial_eval p x)
        (differentiableAt_apply j x)]
      rw [(hasFDerivAt_apply j x).fderiv]
      change MvPolynomial.eval x p * (Pi.single i (1 : ℂ) : ι → ℂ) j +
        x j * fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x (Pi.single i 1) = _
      rw [hp]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      by_cases h : i = j
      · subst j
        simp
        ring
      · simp [Pi.single_eq_of_ne (Ne.symm h), MvPolynomial.pderiv_X_of_ne (Ne.symm h),
          mul_comm]

/-- The full analytic differential is multiplication by the row of evaluated
formal partial derivatives. -/
theorem fderiv_polynomial_eval_apply (p : MvPolynomial ι ℂ)
    (x v : ι → ℂ) :
    fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v =
      ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, fderiv_polynomial_eval_single, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative
