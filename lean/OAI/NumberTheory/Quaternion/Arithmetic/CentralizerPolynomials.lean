import OAI.NumberTheory.Quaternion.Arithmetic.DifferentialGenerators
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential

/-! # Centralizer Polynomials -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CentralizerPolynomials

noncomputable section

/-! Polynomial centralizer equations and their infinitesimal derivatives.
Commuting Lie directions preserve the ideal of these equations. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential.Construction _root_.MvPolynomial

theorem derivation_matrix_mul
    {k A : Type*} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
    (D : Derivation k A A) (M N : Matrix (Fin n) (Fin n) A) :
    (M * N).map D = M * N.map D + M.map D * N := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

variable {k : Type} [Field k] {n : ℕ}

def centralizerMatrixPolynomial (B : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) :=
  let Xmat : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  Xmat * C.mapMatrix B - C.mapMatrix B * Xmat

theorem rightInfinitesimal_centralizerMatrixPolynomial
    (A B : Matrix (Fin n) (Fin n) k) (hAB : A * B = B * A) :
    (centralizerMatrixPolynomial B).map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) =
      centralizerMatrixPolynomial B * C.mapMatrix A := by
  let Xmat : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  let CA : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := C.mapMatrix A
  let CB : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := C.mapMatrix B
  have hX : Xmat.map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) = Xmat * CA := by
    apply Matrix.ext
    intro i j
    exact ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_X A i j
  have hC : CB.map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) = 0 := by
    apply Matrix.ext
    intro i j
    exact ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_C A (B i j)
  have hcomm : CA * CB = CB * CA := by
    change C.mapMatrix A * C.mapMatrix B = C.mapMatrix B * C.mapMatrix A
    rw [← map_mul, ← map_mul, hAB]
  have hsub (M N : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k)) :
      (M - N).map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) =
        M.map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) - N.map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) := by
    apply Matrix.ext
    intro i j
    exact map_sub (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) (M i j) (N i j)
  change (Xmat * CB - CB * Xmat).map (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A) = (Xmat * CB - CB * Xmat) * CA
  rw [hsub, derivation_matrix_mul, derivation_matrix_mul, hX, hC,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.sub_mul]
  simp only [Matrix.mul_assoc, hcomm]

end

end OAI.NumberTheory.Quaternion.Arithmetic.CentralizerPolynomials
