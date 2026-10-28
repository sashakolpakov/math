import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalZariski
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteConnectedAction
import Mathlib.Data.Matrix.Basis

/-! # Adjoint Polynomials -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdjointPolynomials

noncomputable section

/-! Polynomial coordinates for the adjoint action and for linear
functionals of polynomial matrices. These give algebraic closedness of
the stabilizers used in the Lie-ideal argument. -/

open scoped Classical
open _root_.MvPolynomial

variable {k : Type} [Field k] {n : ℕ}

def adjointMatrixPolynomial (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) :=
  let Xmat : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  Xmat * C.mapMatrix A * Xmat.adjugate

theorem evaluate_adjointMatrixPolynomial (g : ArithmeticGroups.Lattices.Algebraic.SL n k) (A : Matrix (Fin n) (Fin n) k) :
    (ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g).mapMatrix (adjointMatrixPolynomial A) =
      (g : Matrix (Fin n) (Fin n) k) * A * ((g⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) := by
  let Xmat : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  let e := ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g
  have hX : e.mapMatrix Xmat = (g : Matrix (Fin n) (Fin n) k) := by
    ext i j
    change e (X (i, j)) = g i j
    simp [e, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  have hC : e.mapMatrix (C.mapMatrix A) = A := by
    ext i j
    simp [e, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  change e.mapMatrix (Xmat * C.mapMatrix A * Xmat.adjugate) = _
  rw [map_mul, map_mul, hX, hC, e.map_adjugate, hX]
  rfl

def linearMatrixPolynomial
    (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (P : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k)) : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k :=
  ∑ i, ∑ j, C (φ (Matrix.single i j 1)) * P i j

theorem evaluate_linearMatrixPolynomial (g : ArithmeticGroups.Lattices.Algebraic.SL n k)
    (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (P : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k)) :
    ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g (linearMatrixPolynomial φ P) =
      φ ((ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g).mapMatrix P) := by
  let e := ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g
  have hC (a : k) : e (C a) = a := by simp [e, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  change e (∑ i, ∑ j, C (φ (Matrix.single i j 1)) * P i j) = φ (e.mapMatrix P)
  rw [Matrix.matrix_eq_sum_single (e.mapMatrix P)]
  simp only [map_sum, map_mul, hC]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.single i j (e (P i j)) = e (P i j) • Matrix.single i j (1 : k) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  change φ (Matrix.single i j 1) * e (P i j) = φ (Matrix.single i j (e (P i j)))
  rw [he, map_smul, smul_eq_mul, mul_comm]

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdjointPolynomials
