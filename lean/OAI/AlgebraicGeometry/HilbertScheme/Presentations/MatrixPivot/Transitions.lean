import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotCokernel

/-! # Transitions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Transitions.Grassmannian

noncomputable section

/-! On a rank-q factorization, every invertible q-by-q coordinate minor satisfies the same pivot equations. This makes pivot overlaps determinant-open. -/

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {μ : Type w} {ν : Type z}
variable [Fintype ι] [DecidableEq ι]

theorem fullPivotResidual_zero_of_width_factorization
    (A : Matrix ν μ R) (E : Matrix ν ι R) (F : Matrix ι μ R) (hA : A = E * F)
    (a : ι → μ) (b : ι → ν) (hu : IsUnit (A.submatrix b a).det) :
    PivotCokernel.Grassmannian.fullPivotResidual A a b = 0 := by
  have hminor : A.submatrix b a = E.submatrix b id * F.submatrix id a := by
    ext i j
    exact congrArg (fun M : Matrix ν μ R => M (b i) (a j)) hA
  have hF : IsUnit (F.submatrix id a).det := by
    rw [hminor, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hcols : A.submatrix id a = E * F.submatrix id a := by
    ext i j
    exact congrArg (fun M : Matrix ν μ R => M i (a j)) hA
  have hfactor : A = A.submatrix id a * ((F.submatrix id a)⁻¹ * F) := by
    rw [hcols, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hF]
    exact hA
  exact PivotCokernel.Grassmannian.fullPivotResidual_zero_of_factorization A a b hu _ hfactor

theorem fullPivotResidual_transition
    (A : Matrix ν μ R) (a c : ι → μ) (b d : ι → ν)
    (hab : IsUnit (A.submatrix b a).det) (hres : PivotCokernel.Grassmannian.fullPivotResidual A a b = 0)
    (hcd : IsUnit (A.submatrix d c).det) : PivotCokernel.Grassmannian.fullPivotResidual A c d = 0 :=
  fullPivotResidual_zero_of_width_factorization A (PivotCokernel.Grassmannian.normalizedPivotColumns A a b) (A.submatrix b id)
    (PivotCokernel.Grassmannian.fullPivotResidual_factorization A a b hab hres) c d hcd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Transitions.Grassmannian
