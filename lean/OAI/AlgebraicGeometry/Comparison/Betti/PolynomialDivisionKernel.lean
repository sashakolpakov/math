import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Polynomial Division Kernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PolynomialDivisionKernel.Weierstrass

noncomputable section

/-! The exact polynomial divided-difference kernel used for holomorphic
division, including its strict degree bound. -/

open _root_.Polynomial

variable {R : Type*} [CommRing R]

theorem polynomial_division_kernel (P : Polynomial R) (z w : R) :
    (z - w) * (P /ₘ (X - C z)).eval w = P.eval z - P.eval w := by
  have h := congrArg (fun Q : Polynomial R => Q.eval w) (P.modByMonic_add_div (X - C z))
  rw [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_C] at h
  linear_combination -h

theorem division_kernel_coeff_zero (P : Polynomial R) (z : R) (k : ℕ)
    (hk : P.natDegree ≤ k) : (P /ₘ (X - C z)).coeff k = 0 := by
  rw [coeff_divByMonic_X_sub_C]
  apply Finset.sum_eq_zero
  intro j hj
  have h := Finset.mem_Icc.mp hj
  omega

variable {K : Type*} [Field K]

theorem polynomial_division_kernel_fraction (P : Polynomial K) (g z w : K)
    (hP : P.eval z ≠ 0) (hzw : z - w ≠ 0) :
    g / P.eval z * (P /ₘ (X - C z)).eval w + P.eval w * (g / (P.eval z * (z - w))) =
      g / (z - w) := by
  have hker : (P /ₘ (X - C z)).eval w = (P.eval z - P.eval w) / (z - w) :=
    (eq_div_iff hzw).2 (by simpa only [mul_comm] using polynomial_division_kernel P z w)
  rw [hker]
  field_simp
  ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.PolynomialDivisionKernel.Weierstrass
