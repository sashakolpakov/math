import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-! # Isolated Pivot Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IsolatedPivotMatrices.Construction

noncomputable section

/-! Inserting an isolated pivot into a matrix respects products and
upper unitriangular matrices. -/

open scoped Classical

def isolatedPivotMatrix {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.insertNth r (Pi.single c a) (fun i => Fin.insertNth c 0 (M i))

@[simp] theorem isolatedPivotMatrix_pivot {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : isolatedPivotMatrix r c M a r c = a := by
  simp [isolatedPivotMatrix]

@[simp] theorem isolatedPivotMatrix_row {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (j : Fin n) :
    isolatedPivotMatrix r c M a r (c.succAbove j) = 0 := by
  simp [isolatedPivotMatrix, c.succAbove_ne j]

@[simp] theorem isolatedPivotMatrix_column {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (i : Fin n) :
    isolatedPivotMatrix r c M a (r.succAbove i) c = 0 := by
  simp [isolatedPivotMatrix]

@[simp] theorem isolatedPivotMatrix_minor {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (i j : Fin n) :
    isolatedPivotMatrix r c M a (r.succAbove i) (c.succAbove j) = M i j := by
  simp [isolatedPivotMatrix]

theorem eq_isolatedPivotMatrix {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ j, j ≠ c → M r j = 0) (hcol : ∀ i, i ≠ r → M i c = 0) :
    M = isolatedPivotMatrix r c (M.submatrix r.succAbove c.succAbove) (M r c) := by
  ext i j
  cases i using Fin.succAboveCases r <;> cases j using Fin.succAboveCases c <;>
    simp [hrow, hcol, Fin.succAbove_ne, Matrix.submatrix_apply]

theorem isolatedPivotMatrix_mul {n : ℕ} (r s t : Fin (n + 1))
    (A B : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) :
    isolatedPivotMatrix r s A a * isolatedPivotMatrix s t B b =
      isolatedPivotMatrix r t (A * B) (a * b) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ s]
  cases i using Fin.succAboveCases r <;> cases j using Fin.succAboveCases t <;>
    simp [Matrix.mul_apply]

theorem isolatedPivotMatrix_unitriangular {n : ℕ} (p : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular M) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (isolatedPivotMatrix p p M 1) := by
  constructor
  · intro i j hij
    change j < i at hij
    cases i using Fin.succAboveCases p with
    | x =>
      cases j using Fin.succAboveCases p with
      | x => exact (lt_irrefl _ hij).elim
      | p j => simp
    | p i =>
      cases j using Fin.succAboveCases p with
      | x => simp
      | p j =>
        rw [isolatedPivotMatrix_minor]
        exact hM.1 ((Fin.succAboveOrderEmb p).lt_iff_lt.mp hij)
  · intro i
    cases i using Fin.succAboveCases p <;> simp [hM.2]

theorem isolatedPivotMatrix_minor_isUnit {n : ℕ} (r c : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (hM : IsUnit (isolatedPivotMatrix r c M a)) : IsUnit M := by
  apply M.isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hdet : (isolatedPivotMatrix r c M a).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((isolatedPivotMatrix r c M a).isUnit_iff_isUnit_det.mp hM)
  apply hdet
  rw [Matrix.det_succ_row _ r]
  apply Finset.sum_eq_zero
  intro j _
  cases j using Fin.succAboveCases c with
  | x =>
    have he : (isolatedPivotMatrix r c M a).submatrix r.succAbove c.succAbove = M := by
      ext i j
      exact isolatedPivotMatrix_minor r c M a i j
    simp [he, hz]
  | p j => simp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IsolatedPivotMatrices.Construction
