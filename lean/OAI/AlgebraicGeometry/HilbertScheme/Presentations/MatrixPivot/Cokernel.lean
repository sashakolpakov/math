import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SchurCokernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Cokernel.Grassmannian

noncomputable section

/-! Polynomial equations on a determinant-open chart identify the actual cokernel with a finite free module. -/

universe u v w z

variable {R : Type u} [CommRing R]
variable {ι : Type v} {κ : Type w} {τ : Type z}
variable [Fintype ι] [Fintype κ] [Fintype τ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

def matrixPivotEquiv (A : Matrix ι ι R) (hA : IsUnit A.det) : (ι → R) ≃ₗ[R] (ι → R) where
  __ := Matrix.toLin' A
  invFun := Matrix.toLin' A⁻¹
  left_inv x := by
    change Matrix.toLin' A⁻¹ (Matrix.toLin' A x) = x
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.nonsing_inv_mul A hA,
      Matrix.toLin'_one, LinearMap.id_apply]
  right_inv x := by
    change Matrix.toLin' A (Matrix.toLin' A⁻¹ x) = x
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv A hA,
      Matrix.toLin'_one, LinearMap.id_apply]

def pivotResidual (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R) :
    Matrix τ κ R := A.det • D - C * A.adjugate * B

omit [Fintype κ] [Fintype τ] [DecidableEq κ] [DecidableEq τ] in
theorem pivotResidual_eq_det_smul_schur
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R)
    (hA : IsUnit A.det) :
    pivotResidual A B C D = A.det • (D - C * A⁻¹ * B) := by
  have hi : A.det • A⁻¹ = A.adjugate := by
    rw [Matrix.nonsing_inv_apply A hA, smul_smul, hA.mul_val_inv, one_smul]
  rw [smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hi]
  rfl

omit [Fintype κ] [Fintype τ] [DecidableEq κ] [DecidableEq τ] in
theorem pivotResidual_zero_iff (A : Matrix ι ι R) (B : Matrix ι κ R)
    (C : Matrix τ ι R) (D : Matrix τ κ R) (hA : IsUnit A.det) :
    pivotResidual A B C D = 0 ↔ D - C * A⁻¹ * B = 0 := by
  rw [pivotResidual_eq_det_smul_schur A B C D hA]
  simpa only [smul_zero] using (hA.smul_left_cancel (x := D - C * A⁻¹ * B) (y := 0))

omit [Fintype τ] [DecidableEq τ] in
theorem matrix_schurComplement_toLin
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R)
    (hA : IsUnit A.det) :
    SchurCokernel.Grassmannian.schurComplement (matrixPivotEquiv A hA) (Matrix.toLin' B) (Matrix.toLin' C) (Matrix.toLin' D) =
      Matrix.toLin' (D - C * A⁻¹ * B) := by
  change Matrix.toLin' D - (Matrix.toLin' C).comp ((Matrix.toLin' A⁻¹).comp (Matrix.toLin' B)) = _
  rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_assoc]

def matrixPivotCokernelEquiv
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R)
    (hA : IsUnit A.det) (h : pivotResidual A B C D = 0) :
    (((ι → R) × (τ → R)) ⧸
      (Grassmannian.Incidence.blockLinearMap (Matrix.toLin' A) (Matrix.toLin' B) (Matrix.toLin' C) (Matrix.toLin' D)).range) ≃ₗ[R]
      (τ → R) :=
  SchurCokernel.Grassmannian.schurZeroCokernelEquiv (matrixPivotEquiv A hA) (Matrix.toLin' B) (Matrix.toLin' C) (Matrix.toLin' D) (by
    rw [matrix_schurComplement_toLin, (pivotResidual_zero_iff A B C D hA).mp h, map_zero])

omit [Fintype κ] [Fintype τ] [DecidableEq κ] [DecidableEq τ] in
theorem pivotResidual_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R) :
    (pivotResidual A B C D).map φ = pivotResidual (A.map φ) (B.map φ) (C.map φ) (D.map φ) := by
  have ha : A.adjugate.map φ = (A.map φ).adjugate := φ.map_adjugate A
  have hd : φ A.det = (A.map φ).det := φ.map_det A
  have hs : (A.det • D).map φ = φ A.det • D.map φ := by
    ext i j
    exact φ.map_mul A.det (D i j)
  simp only [pivotResidual, Matrix.map_sub _ φ.map_sub, Matrix.map_mul, hs, hd, ha]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Cokernel.Grassmannian
