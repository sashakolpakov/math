import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.RationalForm

/-! # Congruence Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CongruencePolynomial.Construction

noncomputable section

/-! Polynomial coordinates and infinitesimal derivatives of the
congruence action on bilinear forms. -/

open scoped Classical
open _root_.Matrix _root_.MvPolynomial

def congruencePolynomial {k : Type} [Field k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) (i j : Fin n) : Algebraic.CoordinatePolynomial n k :=
  ∑ b, (∑ a, X (a, i) * C (Q a b)) * X (b, j)

theorem evaluate_congruencePolynomial
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (g : Algebraic.SL n K) (Q : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix v g (congruencePolynomial Q i j) =
      ((g : Matrix (Fin n) (Fin n) K).transpose * Q.map v *
        (g : Matrix (Fin n) (Fin n) K)) i j := by
  simp [congruencePolynomial, Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem evaluate_infinitesimal_coordinate_matrix_product
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (g : Algebraic.SL n K) (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix v g (Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j))) =
      ((g : Matrix (Fin n) (Fin n) K) * A.map v) i j := by
  simp [Infinitesimal.Action.Construction.rightInfinitesimal_X, Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem derivative_congruencePolynomial_evaluate
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (g : Algebraic.SL n K) (A Q : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix v g (Infinitesimal.Action.Construction.rightInfinitesimal A (congruencePolynomial Q i j)) =
      (((g : Matrix (Fin n) (Fin n) K) * A.map v).transpose * Q.map v *
          (g : Matrix (Fin n) (Fin n) K) +
        (g : Matrix (Fin n) (Fin n) K).transpose * Q.map v *
          ((g : Matrix (Fin n) (Fin n) K) * A.map v)) i j := by
  unfold congruencePolynomial
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    evaluate_infinitesimal_coordinate_matrix_product, Infinitesimal.Action.Construction.rightInfinitesimal_C, mul_zero, zero_add]
  have hC (c : k) : Algebraic.evaluateMatrix v g (C c) = v c := by simp [Algebraic.evaluateMatrix]
  have hX (a b : Fin n) : Algebraic.evaluateMatrix v g (X (a, b)) = g a b := by simp [Algebraic.evaluateMatrix]
  simp only [hC, hX, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CongruencePolynomial.Construction
