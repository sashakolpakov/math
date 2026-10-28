import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-! # Complex Linear Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearHomotopy.Cycles

noncomputable section

/-!
# Paths through invertible complex matrices

The determinant of the pencil `(1-z)I + zA` is a nonzero complex polynomial.
Its finite root set can be avoided by a path from `0` to `1`. Mapping that path
through the pencil produces a path of invertible matrices from `I` to `A`.
This proves the actual homotopy input for later orientation arguments, without
assuming a local homology generator or any fundamental-class theorem.
-/

open _root_.Polynomial

universe u

variable {n : Type u} [DecidableEq n]

/-- The affine complex pencil joining the identity matrix to `A`. -/
def complexMatrixPencil (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (1 - z) • (1 : Matrix n n ℂ) + z • A

@[simp]
theorem complexMatrixPencil_zero (A : Matrix n n ℂ) :
    complexMatrixPencil A 0 = 1 := by
  simp [complexMatrixPencil]

@[simp]
theorem complexMatrixPencil_one (A : Matrix n n ℂ) :
    complexMatrixPencil A 1 = A := by
  simp [complexMatrixPencil]

theorem continuous_complexMatrixPencil (A : Matrix n n ℂ) :
    Continuous (complexMatrixPencil A) :=
  ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

/-- The pencil entries as actual one-variable polynomials. -/
def complexMatrixPolynomial (A : Matrix n n ℂ) : Matrix n n ℂ[X] :=
  fun i j => (1 - Polynomial.X) * Polynomial.C ((1 : Matrix n n ℂ) i j) +
    Polynomial.X * Polynomial.C (A i j)

variable [Fintype n]

/-- The determinant polynomial whose roots are the singular parameters. -/
def complexMatrixDetPolynomial (A : Matrix n n ℂ) : ℂ[X] :=
  (complexMatrixPolynomial A).det

@[simp]
theorem complexMatrixDetPolynomial_eval (A : Matrix n n ℂ) (z : ℂ) :
    (complexMatrixDetPolynomial A).eval z = (complexMatrixPencil A z).det := by
  have hmap : (Polynomial.evalRingHom z).mapMatrix (complexMatrixPolynomial A) =
      complexMatrixPencil A z := by
    ext i j
    simp [complexMatrixPolynomial, complexMatrixPencil, Matrix.smul_apply]
    exact mul_comm _ _
  exact ((Polynomial.evalRingHom z).map_det (complexMatrixPolynomial A)).trans
    (congrArg Matrix.det hmap)

@[simp]
theorem complexMatrixDetPolynomial_eval_zero (A : Matrix n n ℂ) :
    (complexMatrixDetPolynomial A).eval 0 = 1 := by
  simp

@[simp]
theorem complexMatrixDetPolynomial_eval_one (A : Matrix n n ℂ) :
    (complexMatrixDetPolynomial A).eval 1 = A.det := by
  simp

theorem complexMatrixDetPolynomial_ne_zero (A : Matrix n n ℂ) :
    complexMatrixDetPolynomial A ≠ 0 := by
  intro h
  have hz := congrArg (fun q : ℂ[X] => q.eval 0) h
  simp at hz

/-- The singular parameters of the pencil form a finite set. -/
theorem finite_complexMatrixPencil_singular (A : Matrix n n ℂ) :
    Set.Finite {z : ℂ | (complexMatrixPencil A z).det = 0} := by
  simpa only [Polynomial.IsRoot, complexMatrixDetPolynomial_eval] using
    Polynomial.finite_setOfPred_isRoot (complexMatrixDetPolynomial_ne_zero A)

/-- A nonsingular complex matrix can be joined to the identity without crossing
a singular matrix. -/
theorem joinedIn_complexMatrix_det_ne_zero (A : Matrix n n ℂ) (hA : A.det ≠ 0) :
    JoinedIn {M : Matrix n n ℂ | M.det ≠ 0} 1 A := by
  let S : Set ℂ := {z : ℂ | (complexMatrixPencil A z).det = 0}ᶜ
  have hS : IsPathConnected S :=
    (finite_complexMatrixPencil_singular A).countable.isPathConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex])
  have h0 : (0 : ℂ) ∈ S := by simp [S]
  have h1 : (1 : ℂ) ∈ S := by simpa [S] using hA
  have hpath := (hS.joinedIn 0 h0 1 h1).map (continuous_complexMatrixPencil A).continuousOn
  have hrange : complexMatrixPencil A '' S ⊆ {M : Matrix n n ℂ | M.det ≠ 0} := by
    rintro M ⟨z, hz, rfl⟩
    exact hz
  simpa only [complexMatrixPencil_zero, complexMatrixPencil_one] using hpath.mono hrange

/-- The group of invertible complex matrices is path connected, expressed as
the actual invertible subset of matrix space. -/
theorem isPathConnected_invertible_complexMatrices :
    IsPathConnected {M : Matrix n n ℂ | IsUnit M} := by
  refine ⟨1, isUnit_one, ?_⟩
  intro A hA
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  apply (joinedIn_complexMatrix_det_ne_zero A hdet).mono
  intro M hM
  exact (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)

/-- A chosen genuine path of invertible matrices from the identity to `A`. -/
def complexMatrixPath (A : Matrix n n ℂ) (hA : IsUnit A) :
    Path (1 : Matrix n n ℂ) A :=
  (isPathConnected_invertible_complexMatrices.joinedIn 1 isUnit_one A hA).somePath

theorem complexMatrixPath_isUnit (A : Matrix n n ℂ) (hA : IsUnit A)
    (t : unitInterval) : IsUnit (complexMatrixPath A hA t) :=
  (isPathConnected_invertible_complexMatrices.joinedIn 1 isUnit_one A hA).somePath_mem t

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearHomotopy.Cycles
