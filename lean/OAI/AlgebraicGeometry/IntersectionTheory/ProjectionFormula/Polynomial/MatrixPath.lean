import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Matrix Path -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

noncomputable section

/-! A polynomial matrix path connects the identity to a prescribed
invertible matrix. Localizing at its determinant gives an actual family
of invertible matrices, with both endpoint evaluations retained. -/

set_option backward.isDefEq.respectTransparency false

open scoped _root_.Polynomial

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

def matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ[X] :=
  fun i j => (1 - Polynomial.X) * Polynomial.C ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j) +
    Polynomial.X * Polynomial.C (A.val i j)

theorem eval_zero : (Polynomial.evalRingHom 0).mapMatrix (matrix A) = 1 := by
  ext i j
  simp [matrix]

theorem eval_one : (Polynomial.evalRingHom 1).mapMatrix (matrix A) = A.val := by
  ext i j
  simp [matrix]

def determinant : ℂ[X] := (matrix A).det

theorem determinant_zero : (determinant A).eval 0 = 1 := by
  change (Polynomial.evalRingHom 0) (matrix A).det = 1
  rw [RingHom.map_det, MatrixPath.eval_zero, Matrix.det_one]

theorem determinant_one : (determinant A).eval 1 = A.val.det := by
  change (Polynomial.evalRingHom 1) (matrix A).det = _
  rw [RingHom.map_det, eval_one]

theorem determinant_ne_zero : determinant A ≠ 0 := by
  intro h
  have hz := determinant_zero A
  rw [h, Polynomial.eval_zero] at hz
  exact zero_ne_one hz

theorem finite_bad_parameters : Set.Finite {t : ℂ | (determinant A).eval t = 0} :=
  Polynomial.finite_setOfPred_isRoot (determinant_ne_zero A)

abbrev Ring := Localization.Away (determinant A)

def localizedMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ring A) :=
  (algebraMap ℂ[X] (Ring A)).mapMatrix (matrix A)

theorem localized_isUnit : IsUnit (localizedMatrix A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [localizedMatrix, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (determinant A)

def unit : (Matrix (Fin (n + 1)) (Fin (n + 1)) (Ring A))ˣ := (localized_isUnit A).unit

theorem unit_val : (MatrixPath.unit A).val = localizedMatrix A := (localized_isUnit A).unit_spec

def evaluation (t : ℂ) (ht : (determinant A).eval t ≠ 0) : Ring A →+* ℂ :=
  IsLocalization.Away.lift (determinant A) (g := Polynomial.evalRingHom t) (isUnit_iff_ne_zero.mpr ht)

theorem evaluation_algebraMap (t : ℂ) (ht : (determinant A).eval t ≠ 0) (p : ℂ[X]) :
    evaluation A t ht (algebraMap ℂ[X] (Ring A) p) = p.eval t :=
  IsLocalization.Away.lift_eq _ _ p

theorem evaluate_unit (t : ℂ) (ht : (determinant A).eval t ≠ 0) :
    (evaluation A t ht).mapMatrix (MatrixPath.unit A).val = (Polynomial.evalRingHom t).mapMatrix (matrix A) := by
  rw [unit_val]
  ext i j
  exact evaluation_algebraMap A t ht (matrix A i j)

theorem evaluate_zero (h : (determinant A).eval 0 ≠ 0) :
    (evaluation A 0 h).mapMatrix (MatrixPath.unit A).val = 1 := (evaluate_unit A 0 h).trans (MatrixPath.eval_zero A)

theorem evaluate_one (h : (determinant A).eval 1 ≠ 0) :
    (evaluation A 1 h).mapMatrix (MatrixPath.unit A).val = A.val := (evaluate_unit A 1 h).trans (eval_one A)

theorem zero_good : (determinant A).eval 0 ≠ 0 := by rw [determinant_zero]; exact one_ne_zero

theorem one_good : (determinant A).eval 1 ≠ 0 := by
  rw [determinant_one]
  exact (Matrix.isUnits_det_units A).ne_zero

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath
