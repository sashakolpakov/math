import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Linear Form Matrix -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormMatrix

noncomputable section

/-! The action of a linear-form automorphism is the action of its
actual invertible coefficient matrix on projective coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis

variable {n : ℕ}

def matrix (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (LinearMap.toMatrix (LinearFormBasis.basis n) (LinearFormBasis.basis n) F).transpose

theorem matrix_comp (F G : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    matrix (G.comp F) = matrix F * matrix G := by
  rw [matrix, LinearMap.toMatrix_comp (LinearFormBasis.basis n) (LinearFormBasis.basis n) (LinearFormBasis.basis n), Matrix.transpose_mul]
  rfl

theorem matrix_id : matrix (LinearMap.id : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) = 1 := by
  rw [matrix, LinearMap.toMatrix_id, Matrix.transpose_one]

def unit (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ where
  val := matrix e.toLinearMap
  inv := matrix e.symm.toLinearMap
  val_inv := by
    rw [← matrix_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    rw [h, matrix_id]
  inv_val := by
    rw [← matrix_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply x
    rw [h, matrix_id]

theorem form (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (i : Fin (n + 1)) :
    Projective.LinearChart.Coordinates.form (matrix F) i = (F (LinearFormBasis.coordinate n i)).val := by
  have h := congrArg Subtype.val ((LinearFormBasis.basis n).sum_repr (F (LinearFormBasis.coordinate n i)))
  simpa only [Projective.LinearChart.Coordinates.form, matrix, Matrix.transpose_apply,
    LinearMap.toMatrix_apply, LinearFormBasis.basis_apply, Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul, LinearFormBasis.coordinate] using h

theorem graded (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    Projective.LinearChart.Coordinates.gradedHom (unit e).val = LinearFormBasis.GradedMap.gradedHom e.toLinearMap := by
  have h : Projective.LinearChart.Coordinates.algebraHom (unit e).val =
      LinearFormBasis.GradedMap.algebraHom e.toLinearMap := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Projective.LinearChart.Coordinates.algebraHom_X, LinearFormBasis.GradedMap.algebraHom_X]
    exact form e.toLinearMap i
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun h p

theorem map (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    Projective.LinearChart.Automorphism.map (unit e) = LinearFormAutomorphism.map e := by
  unfold Projective.LinearChart.Automorphism.map LinearFormAutomorphism.map
  simp only [graded]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormMatrix
