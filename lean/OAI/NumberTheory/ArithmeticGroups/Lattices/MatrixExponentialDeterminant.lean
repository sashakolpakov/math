import OAI.NumberTheory.ArithmeticGroups.Lattices.DeterminantDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialPolynomial

/-! # Matrix Exponential Determinant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixExponentialDeterminant.Construction

noncomputable section

/-! The determinant of a matrix exponential is the exponential of its
trace, proved by differentiating along the exponential curve. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace

variable {k : Type} [RCLike k] {n : ℕ}

theorem matrix_exp_det_hasDerivAt (A : Matrix (Fin n) (Fin n) k) (t : k) :
    HasDerivAt (fun s : k => (exp (s • A)).det) ((exp (t • A)).det * A.trace) t := by
  have h := ExponentialPolynomial.Construction.exponentialPolynomial_hasDerivAt A (DeterminantDerivative.Construction.determinantPolynomial k n) t
  unfold ExponentialPolynomial.Construction.exponentialPolynomial at h
  simpa only [DeterminantDerivative.Construction.eval_determinantPolynomial, DeterminantDerivative.Construction.eval_rightInfinitesimal_determinantPolynomial] using h

theorem matrix_exp_det_integratingFactor (A : Matrix (Fin n) (Fin n) k) (t : k) :
    HasDerivAt (fun s : k => (exp (s • A)).det * exp (s * (-A.trace))) 0 t := by
  have he := hasDerivAt_exp_smul_const (-A.trace) t
  simp only [smul_eq_mul] at he
  convert! (matrix_exp_det_hasDerivAt A t).mul he using 1
  ring

theorem matrix_exp_det_smul (A : Matrix (Fin n) (Fin n) k) (t : k) :
    (exp (t • A)).det = exp (t * A.trace) := by
  have hc := is_const_of_deriv_eq_zero
    (fun s => (matrix_exp_det_integratingFactor A s).differentiableAt)
    (fun s => (matrix_exp_det_integratingFactor A s).deriv) t 0
  simp only [zero_smul, exp_zero, Matrix.det_one, zero_mul, one_mul, mul_neg] at hc
  have he := congrArg (fun z : k => z * exp (t * A.trace)) hc
  have hcancel : exp (-(t * A.trace)) * exp (t * A.trace) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.all _ _), neg_add_cancel, exp_zero]
  simpa only [mul_assoc, hcancel, mul_one, one_mul, neg_zero, exp_zero] using he

theorem matrix_exp_det (A : Matrix (Fin n) (Fin n) k) : (exp A).det = exp A.trace := by
  simpa only [one_smul, one_mul] using matrix_exp_det_smul A 1

theorem matrix_exp_det_one_of_trace_zero {A : Matrix (Fin n) (Fin n) k}
    (hA : A.trace = 0) : (exp A).det = 1 := by
  rw [matrix_exp_det, hA, exp_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixExponentialDeterminant.Construction
