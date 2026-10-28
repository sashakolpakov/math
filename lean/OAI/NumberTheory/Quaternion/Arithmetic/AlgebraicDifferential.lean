import OAI.NumberTheory.Quaternion.Arithmetic.MatrixDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Algebraic Differential -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicDifferential

noncomputable section

/-! Identification of the analytic matrix differential at the identity
with the algebraic infinitesimal right action. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action.Construction _root_.MvPolynomial

variable {K : Type} [NontriviallyNormedField K] {n : ℕ}

theorem evaluate_rightInfinitesimal_X_one (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id K) (1 : ArithmeticGroups.Lattices.Algebraic.SL n K) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j))) = A i j := by
  simp [ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_X, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, Matrix.one_apply]

theorem matrixPolynomialDifferential_eq_rightInfinitesimal
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K) (A : Matrix (Fin n) (Fin n) K) :
    MatrixDifferential.matrixPolynomialDifferential p 1 A =
      ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id K) (1 : ArithmeticGroups.Lattices.Algebraic.SL n K) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A p) := by
  change MatrixDifferential.polynomialDifferential p (MatrixDifferential.matrixEntriesLinear 1) (MatrixDifferential.matrixEntriesLinear A) = _
  induction p using MvPolynomial.induction_on with
  | C a => simp [MatrixDifferential.polynomialDifferential_C]
  | add p q hp hq =>
    rw [MatrixDifferential.polynomialDifferential_add]
    simp only [add_apply, map_add, hp, hq]
  | mul_X p ij hp =>
    rcases ij with ⟨i, j⟩
    rw [MatrixDifferential.polynomialDifferential_mul_X]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Derivation.leibniz, map_add, map_mul,
      evaluate_rightInfinitesimal_X_one, hp]
    simp only [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, MvPolynomial.eval₂Hom_X', Matrix.SpecialLinearGroup.coe_one]
    rfl

theorem matrixTangentSpan_satisfies_infinitesimal_equations
    {F : Type} [Field F] (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K)
    (hp : ∀ g ∈ H, eval (fun ij => g.val ij.1 ij.2) p = 0)
    {A : Matrix (Fin n) (Fin n) K} (hA : A ∈ TangentCone.matrixTangentSpan G ι H) :
    ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id K) (1 : ArithmeticGroups.Lattices.Algebraic.SL n K) (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A p) = 0 := by
  rw [← matrixPolynomialDifferential_eq_rightInfinitesimal]
  exact MatrixDifferential.matrixTangentSpan_le_equation_kernel G ι H p hp hA

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicDifferential
